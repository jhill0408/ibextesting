/*
 * File:    verif_client.rs
 * Brief:   TODO
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * TODO
 *
*/

/*!
 * TODO rustdoc for this file here
*/

/* ------------------------------------------------------------------------------------------------
 * Submodules
 * --------------------------------------------------------------------------------------------- */

mod check;
mod stats;

/* ------------------------------------------------------------------------------------------------
 * Uses
 * --------------------------------------------------------------------------------------------- */

pub use check::check;
pub use stats::VerifClientStats;

use crate::parse::{ParsedMessages, VerifClientMessage};

/* ------------------------------------------------------------------------------------------------
 * Macros
 * --------------------------------------------------------------------------------------------- */

//TODO (also pub(crate) use the_macro statements here too)

/* ------------------------------------------------------------------------------------------------
 * Constants
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Static Variables
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Types
 * --------------------------------------------------------------------------------------------- */

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct PacketInfo {
    src:        u32,//May be from a parsed Sent, or based on the data (packetid) of a Received
    dest:       u32,
    vc:         u32,
    seq_num:    u32,//The packet number, based on the data (packetid)
}

#[derive(Copy, Clone, Debug)]
enum PacketOperationType {
    Sent,
    Received
}

#[derive(Clone, Debug)]
struct PacketOperation {
    time:       u64,
    operation:  PacketOperationType,
    info:       PacketInfo,
}

#[derive(Debug)]
pub struct PacketOperations {
    n_value:    usize,
    vc_w_value: usize,
    operations: Vec<PacketOperation>,
}

/* ------------------------------------------------------------------------------------------------
 * Associated Functions and Methods
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Traits And Default Implementations
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Trait Implementations
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

pub fn interpret(messages: &ParsedMessages) -> Result<Option<PacketOperations>, String> {
    let messages = messages.get_verif_client_messages();
    if let Some((n_value, vc_w_value)) = find_info(&messages)? {
        println!("Detected N = {}, VC_W = {}", n_value, vc_w_value);
        let packet_operations = interpret_packet_operations(messages, n_value)?;

        Ok(Some(PacketOperations{
            n_value:    n_value,
            vc_w_value: vc_w_value,
            operations: packet_operations
        }))
    } else {
        Ok(None)
    }
}

fn find_info(messages: &[VerifClientMessage]) -> Result<Option<(usize, usize)>, String> {
    let mut result = Ok(None);

    for message in messages {
        if let VerifClientMessage::Info{n_value, vc_w_value, ..} = message {
            if let Ok(Some(_)) = &result {
                return Err("Multiple Info messages found in log".to_string());
            }
            result = Ok(Some((*n_value, *vc_w_value)));
        }
    }

    result
}

fn interpret_packet_operations(messages: &[VerifClientMessage], n_value: usize) -> Result<Vec<PacketOperation>, String> {
    Ok(messages.iter().filter_map(|message| {
        match *message {
            VerifClientMessage::Sent{time, src, dest, vc, data} => {
                let (data_src, seq_num) = src_and_seq_num_from_data(data, n_value);
                assert_eq!(data_from_src_and_seq_num(data_src, seq_num, n_value), data);
                if data_src != src {
                    println!("Packet sent with src={}, but data indicates src={}", src, data_src);
                    panic!();//TODO handle this error nicer through the iterator with the Result return type
                }
                Some(PacketOperation{time, operation: PacketOperationType::Sent, info: PacketInfo{src, dest, vc, seq_num}})
            },
            VerifClientMessage::Received{time, dest, vc, data} => {
                let (src, seq_num) = src_and_seq_num_from_data(data, n_value);
                assert_eq!(data_from_src_and_seq_num(src, seq_num, n_value), data);
                Some(PacketOperation{time, operation: PacketOperationType::Received, info: PacketInfo{src, dest, vc, seq_num}})
            },
            _ => None
        }
    }).collect())
}

fn src_and_seq_num_from_data(data: u128, n_value: usize) -> (u32, u32) {
    //Helper to determine the source and sequence num of the packet based on the data
    let src     = (data % (n_value as u128)) as u32;
    let seq_num = (data / (n_value as u128)) as u32;
    (src, seq_num)
}

fn data_from_src_and_seq_num(src: u32, seq_num: u32, n_value: usize) -> u128 {
    (seq_num as u128) * (n_value as u128) + (src as u128)
}

/* ------------------------------------------------------------------------------------------------
 * Tests
 * --------------------------------------------------------------------------------------------- */

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanity_src_and_seq_num_from_data() {
        assert_eq!(src_and_seq_num_from_data(0, 5), (0, 0));
        assert_eq!(src_and_seq_num_from_data(1, 5), (1, 0));
        assert_eq!(src_and_seq_num_from_data(2, 5), (2, 0));
        assert_eq!(src_and_seq_num_from_data(3, 5), (3, 0));
        assert_eq!(src_and_seq_num_from_data(4, 5), (4, 0));
        assert_eq!(src_and_seq_num_from_data(5, 5), (0, 1));
        assert_eq!(src_and_seq_num_from_data(6, 5), (1, 1));
        assert_eq!(src_and_seq_num_from_data(7, 5), (2, 1));
        assert_eq!(src_and_seq_num_from_data(8, 5), (3, 1));
        assert_eq!(src_and_seq_num_from_data(9, 5), (4, 1));
        assert_eq!(src_and_seq_num_from_data(10, 5), (0, 2));
    }

    #[test]
    fn sanity_data_from_src_and_seq_num() {
        assert_eq!(data_from_src_and_seq_num(0, 0, 5), 0);
        assert_eq!(data_from_src_and_seq_num(1, 0, 5), 1);
        assert_eq!(data_from_src_and_seq_num(2, 0, 5), 2);
        assert_eq!(data_from_src_and_seq_num(3, 0, 5), 3);
        assert_eq!(data_from_src_and_seq_num(4, 0, 5), 4);
        assert_eq!(data_from_src_and_seq_num(0, 1, 5), 5);
        assert_eq!(data_from_src_and_seq_num(1, 1, 5), 6);
        assert_eq!(data_from_src_and_seq_num(2, 1, 5), 7);
        assert_eq!(data_from_src_and_seq_num(3, 1, 5), 8);
        assert_eq!(data_from_src_and_seq_num(4, 1, 5), 9);
        assert_eq!(data_from_src_and_seq_num(0, 2, 5), 10);
    }

    //TODO more tests
}

/* ------------------------------------------------------------------------------------------------
 * Benchmarks
 * --------------------------------------------------------------------------------------------- */

//TODO
