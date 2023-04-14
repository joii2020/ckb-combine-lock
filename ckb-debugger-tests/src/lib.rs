#[allow(dead_code)]
pub mod combine_lock_mol;
mod hash;
mod smt;

pub mod blockchain {
    pub use ckb_types::packed::{
        Byte, Byte32, Byte32Reader, Byte32Vec, Byte32VecReader, ByteReader, Bytes, BytesOpt,
        BytesOptReader, BytesReader, BytesVec, BytesVecReader, Script, WitnessArgs,
        WitnessArgsBuilder, WitnessArgsReader,
    };
}
use anyhow;
use anyhow::Context;
use blockchain::Bytes as BlockchainBytes;
use blockchain::WitnessArgs;
use ckb_hash::new_blake2b;
use ckb_types::core::ScriptHashType;
use ckb_types::packed;
use ckb_types::prelude::*;
use combine_lock_mol::{ChildScript, ChildScriptVec, CombineLockWitness, Uint16};
use molecule::bytes::Bytes;
use molecule::prelude::*;
use std::{collections::HashSet, fs::read_to_string, path::PathBuf};

use ckb_debugger_api::embed::Embed;
use ckb_mock_tx_types::{MockTransaction, ReprMockTransaction};
use hash::hash;
use serde_json::from_str as from_json_str;
use smt::build_tree;
use sparse_merkle_tree::H256;

pub fn read_tx_template(file_name: &str) -> Result<MockTransaction, anyhow::Error> {
    let mock_tx =
        read_to_string(file_name).with_context(|| format!("Failed to read from {}", file_name))?;
    let mut mock_tx_embed = Embed::new(PathBuf::from(file_name), mock_tx.clone());
    let mock_tx = mock_tx_embed.replace_all();
    let repr_mock_tx: ReprMockTransaction =
        from_json_str(&mock_tx).with_context(|| "in from_json_str(&mock_tx)")?;
    Ok(repr_mock_tx.into())
}

pub fn create_script_from_cell_dep(
    tx: &ReprMockTransaction,
    index: usize,
    use_type: bool,
) -> Result<packed::Script, anyhow::Error> {
    assert!(index < tx.mock_info.cell_deps.len());
    let code_hash = if use_type {
        let cell_dep = &tx.mock_info.cell_deps[index];
        let script = cell_dep.output.type_.clone().unwrap();
        let script: packed::Script = script.into();
        hash(script.as_slice())
    } else {
        let data = tx.mock_info.cell_deps[index].data.as_bytes();
        hash(data)
    };
    let hash_type = if use_type {
        ScriptHashType::Type
    } else {
        ScriptHashType::Data1
    };
    let script = packed::Script::new_builder()
        .code_hash(code_hash.pack())
        .hash_type(hash_type.into())
        .build();
    Ok(script)
}

// return smt root, witness args
pub fn create_simple_case(scripts: Vec<ChildScript>) -> (H256, Bytes) {
    let builder = ChildScriptVec::new_builder();
    let child_scripts = builder.extend(scripts).build();

    let h = hash(child_scripts.as_slice());
    let (root, proof) = build_tree(&Vec::from([h]));

    let index = Uint16::new_builder().nth0(1u8.into()).build();
    let proof: Bytes = proof.into();
    let proof2: BlockchainBytes = proof.pack();
    let combine_lock_witness = CombineLockWitness::new_builder()
        .scripts(child_scripts)
        .proof(proof2)
        .witness_base_index(index)
        .build();
    let bytes = combine_lock_witness.as_bytes();
    let witness_args = WitnessArgs::new_builder().lock(Some(bytes).pack()).build();

    (root, witness_args.as_bytes())
}

impl From<packed::Script> for ChildScript {
    fn from(value: packed::Script) -> Self {
        ChildScript::new_unchecked(value.as_bytes())
    }
}

// Now, only support lock script
fn get_index_by_group_index(group_index: usize, tx: &MockTransaction) -> Vec<usize> {
    let mut r = Vec::<usize>::new();

    let repr_tx: ReprMockTransaction = tx.clone().into();
    let mut group_index = group_index;
    let mut hash_buf = HashSet::<[u8; 32]>::new();

    let mut cur_script_hash: Option<[u8; 32]> = None;

    for i in 0..repr_tx.mock_info.inputs.len() {
        let input_cell = repr_tx.mock_info.inputs.get(i).unwrap();
        let msg = {
            let script = &input_cell.output.lock;

            let mut ctx = new_blake2b();
            ctx.update(script.code_hash.as_bytes());
            ctx.update(script.args.as_bytes());
            ctx.update(&[script.hash_type.clone() as u8]);
            let mut msg = [0u8; 32];
            ctx.finalize(&mut msg);
            msg
        };

        if group_index == 0 {
            if cur_script_hash.is_none() {
                cur_script_hash = Some(msg.clone());
                r.push(i);
            } else {
                if cur_script_hash.eq(&Some(msg.clone())) {
                    r.push(i);
                }
            }
        } else if hash_buf.get(&msg).is_none() {
            hash_buf.insert(msg.clone());
            group_index -= 1;
        }
    }

    r
}

pub fn generate_sighash_all(
    tx: &MockTransaction,
    group_index: usize,
) -> Result<[u8; 32], anyhow::Error> {
    let lock_indexs = get_index_by_group_index(group_index, tx);

    let zero_extra_witness = {
        let mut buf = Vec::new();
        let witness = tx
            .tx
            .witnesses()
            .get(lock_indexs[0])
            .expect("index:0 witness");
        buf.resize(witness.len() - 20, 0);
        buf
    };

    let witness_args = packed::WitnessArgsBuilder::default()
        .lock(Some(Bytes::from(zero_extra_witness)).pack())
        .build();

    let mut blake2b = new_blake2b();
    let mut message = [0u8; 32];

    let tx_hash = tx.tx.calc_tx_hash();
    blake2b.update(&tx_hash.raw_data());
    // println!("--hash: {:02X?}", &tx_hash.raw_data().to_vec());
    let witness_data = witness_args.as_bytes();
    blake2b.update(&(witness_data.len() as u64).to_le_bytes());
    // println!(
    //     "--hash: {:02X?}",
    //     &(witness_data.len() as u64).to_le_bytes()
    // );
    blake2b.update(&witness_data);
    // println!("--hash: {:02X?}", &witness_data.to_vec());

    // group
    if lock_indexs.len() > 1 {
        for i in 1..lock_indexs.len() {}
    }

    // for...
    // ((lock_indexs[0] + 1)..(lock_indexs[0] + tx.mock_info.inputs.len())).for_each(|n| {
    //     let witness = tx.tx.witnesses().get(n).unwrap();
    //     let witness_len = witness.raw_data().len() as u64;
    //     blake2b.update(&witness_len.to_le_bytes());
    //     // println!("--hash: {:02X?}", &witness_len.to_le_bytes());

    //     blake2b.update(&witness.raw_data());
    //     // println!("--hash: {:02X?}", &witness.raw_data().to_vec());
    // });

    blake2b.finalize(&mut message);
    Ok(message)
}
