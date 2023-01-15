extern crate hex;
use bellman_ce::pairing::bn256::Bn256 as Bn256ce;
use memmap::MmapOptions;
use powersoftau::{
    batched_accumulator::BatchedAccumulator,
    keypair::keypair,
    parameters::{CeremonyParams, CheckForCorrectness, UseCompression},
    utils::calculate_hash,
};
use rayon::prelude::*;
use std::{
    fs::{self, OpenOptions},
    io::BufWriter,
};

use std::io::Write;
extern crate hex_literal;

const INPUT_IS_COMPRESSED: UseCompression = UseCompression::No;
const COMPRESS_THE_OUTPUT: UseCompression = UseCompression::Yes;
const CHECK_INPUT_CORRECTNESS: CheckForCorrectness = CheckForCorrectness::No;

// from halo2
use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve, Group as _};
use halo2_proofs::{
    arithmetic::{best_fft, best_multiexp, g_to_lagrange, parallelize, CurveExt, FieldExt, Group},
    halo2curves::{
        bn256::{Bn256, Fq, Fq2, G1Affine, G2Affine},
        pairing::Engine,
        serde::SerdeObject,
        CurveAffine,
    },
    poly::commitment::{Blind, CommitmentScheme, Params, ParamsProver, ParamsVerifier, MSM},
    poly::{Coeff, LagrangeCoeff, Polynomial},
};
use std::fmt::Debug;
use std::io;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign};

// convert_to_halo2 powersOfTau28_hez_final.ptau response_beacon 28 8192 [beaconHash] 10
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 7 {
        println!("Usage: \n<challenge_file> <response_file> <circuit_power> <batch_size> <beacon_hash> <num_iterations_exp>");
        std::process::exit(exitcode::USAGE);
    }
    let challenge_filename = &args[1];
    let response_filename = &args[2];
    let circuit_power = args[3].parse().expect("could not parse circuit power");
    let batch_size = args[4].parse().expect("could not parse batch size");
    let beacon_hash = &args[5];
    let num_iterations_exp = &args[6].parse::<usize>().unwrap();

    if *num_iterations_exp < 10 || *num_iterations_exp > 63 {
        println!("in_num_iterations_exp should be in [10, 63] range");
        std::process::exit(exitcode::DATAERR);
    }

    let parameters = CeremonyParams::<Bn256ce>::new(circuit_power, batch_size);

    println!(
        "Will contribute a random beacon to accumulator for 2^{} powers of tau",
        parameters.size,
    );
    println!(
        "In total will generate up to {} powers",
        parameters.powers_g1_length,
    );

    // Try to load challenge file from disk.
    let reader = OpenOptions::new()
        .read(true)
        .open(challenge_filename)
        .expect("unable open challenge file in this directory");

    {
        let metadata = reader
            .metadata()
            .expect("unable to get filesystem metadata for challenge file");
        let expected_challenge_length = match INPUT_IS_COMPRESSED {
            UseCompression::Yes => parameters.contribution_size,
            UseCompression::No => parameters.accumulator_size,
        };

        if metadata.len() != (expected_challenge_length as u64) {
            panic!(
                "The size of challenge file should be {}, but it's {}, so something isn't right.",
                expected_challenge_length,
                metadata.len()
            );
        }
    }

    let readable_map = unsafe {
        MmapOptions::new()
            .map(&reader)
            .expect("unable to create a memory map for input")
    };

    let mut accumulator = BatchedAccumulator::<Bn256ce>::deserialize(
        &readable_map,
        CHECK_INPUT_CORRECTNESS,
        INPUT_IS_COMPRESSED,
        &parameters,
    )
    .expect("must transform with the key");

    let largest_k = 25;
    let k = largest_k; // circuit_power as u32;
    assert!(k <= <Bn256 as Engine>::Scalar::S);
    let n: u64 = 1 << k;

    let fq_ce_to_fq = |x: bellman_ce::pairing::bn256::Fq| {
        // raw montgomery form, LE
        let x = x.0 .0;
        let mut bytes = [0u8; 32];
        for i in 0..4 {
            bytes[i * 8..(i + 1) * 8].copy_from_slice(&x[i].to_le_bytes());
        }
        Fq::from_raw_bytes(&bytes).unwrap()
    };
    println!("finished reading challenge file");
    accumulator.tau_powers_g1.truncate(n as usize);
    let g = accumulator
        .tau_powers_g1
        .into_par_iter()
        .map(|g| {
            let x = fq_ce_to_fq(g.get_x());
            let y = fq_ce_to_fq(g.get_y());
            G1Affine { x, y }
        })
        .collect::<Vec<_>>();
    println!("g_to_lagrange");
    let g_lagrange = g_to_lagrange::<G1Affine>(g.iter().map(|g| g.to_curve()).collect(), k);
    println!("finish g_to_lagrange");

    let g2_ce_to_g2 = |g2: bellman_ce::pairing::bn256::G2Affine| {
        let x = g2.get_x();
        let x = Fq2 {
            c0: fq_ce_to_fq(x.c0),
            c1: fq_ce_to_fq(x.c1),
        };
        let y = g2.get_y();
        let y = Fq2 {
            c0: fq_ce_to_fq(y.c0),
            c1: fq_ce_to_fq(y.c1),
        };
        G2Affine { x, y }
    };
    let g2 = g2_ce_to_g2(accumulator.tau_powers_g2[0]);
    let s_g2 = g2_ce_to_g2(accumulator.tau_powers_g2[1]);

    let mut params = ParamsKZG::<Bn256> {
        k,
        n,
        g,
        g_lagrange,
        g2,
        s_g2,
    };

    fs::create_dir_all("params").unwrap();
    params
        .write(&mut BufWriter::new(
            fs::File::create(format!("params/kzg_bn254_{k}.srs")).unwrap(),
        ))
        .unwrap();
    println!("Wrote params/kzg_bn254_{k}.srs");
    for k in (18..largest_k).rev() {
        params.downsize(k);
        params
            .write(&mut BufWriter::new(
                fs::File::create(format!("params/kzg_bn254_{k}.srs")).unwrap(),
            ))
            .unwrap();
        println!("Wrote params/kzg_bn254_{k}.srs");
    }
}

/// These are the public parameters for the polynomial commitment scheme.
#[derive(Debug, Clone)]
pub struct ParamsKZG<E: Engine> {
    pub k: u32,
    pub n: u64,
    pub g: Vec<E::G1Affine>,
    pub g_lagrange: Vec<E::G1Affine>,
    pub g2: E::G2Affine,
    pub s_g2: E::G2Affine,
}

impl<'params, E: Engine + Debug> ParamsKZG<E>
where
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    fn k(&self) -> u32 {
        self.k
    }

    fn n(&self) -> u64 {
        self.n
    }

    fn downsize(&mut self, k: u32) {
        assert!(k <= self.k);

        self.k = k;
        self.n = 1 << k;

        self.g.truncate(self.n as usize);
        self.g_lagrange = g_to_lagrange(self.g.iter().map(|g| g.to_curve()).collect(), k);
    }

    fn commit_lagrange(
        &self,
        poly: &Polynomial<E::Scalar, LagrangeCoeff>,
        _: Blind<E::Scalar>,
    ) -> E::G1 {
        let size = poly.len();
        assert!(self.n() >= size as u64);
        best_multiexp(poly, &self.g_lagrange[0..size])
    }

    /// Writes params to a buffer.
    fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        for el in self.g.iter() {
            el.write(writer)?;
        }
        for el in self.g_lagrange.iter() {
            el.write(writer)?;
        }
        self.g2.write(writer)?;
        self.s_g2.write(writer)?;
        Ok(())
    }
}

pub trait SerdeCurveAffine: CurveAffine + SerdeObject {
    /// Reads a curve element from raw bytes.
    /// The curve element is stored exactly as it is in memory (two field elements in Montgomery representation).
    fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        Self::read_raw(reader)
    }
    /// Writes a curve element into raw bytes.
    /// The curve element is stored exactly as it is in memory (two field elements in Montgomery representation).
    fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write_raw(writer)
    }
}
impl<C: CurveAffine + SerdeObject> SerdeCurveAffine for C {}
