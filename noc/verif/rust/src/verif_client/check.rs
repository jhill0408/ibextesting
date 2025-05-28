/*
 * File:    check.rs
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

//TODO (includes "mod ..." and "pub mod ...")

/* ------------------------------------------------------------------------------------------------
 * Uses
 * --------------------------------------------------------------------------------------------- */

use crate::make_array;

use super::{PacketOperation, PacketOperationType, PacketInfo, PacketOperations};

use std::collections::HashMap;

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

//TODO

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

pub fn check(packet_operations: &PacketOperations) -> Result<(), String> {
    check_routing_and_connectivity(&packet_operations.operations)?;
    check_inorderness(packet_operations.n_value, packet_operations.vc_w_value, &packet_operations.operations)?;
    println!("All verif_client checks passed!");
    Ok(())
}

fn check_routing_and_connectivity(operations: &[PacketOperation]) -> Result<(), String> {
    println!("Performing routing and connectivity check...");

    //Maps to the time the packet was sent, and also useful to detect duplicates
    let mut packet_sent_tracker: HashMap<PacketInfo, u64> = HashMap::new();

    //Have a failed flag so we keep going and print all errors
    let mut failed = false;
    
    for operation in operations {
        match operation {
            PacketOperation{time, operation: PacketOperationType::Sent, info: PacketInfo{src, dest, vc, seq_num}} => {
                if src == dest {
                    println!("Self packet sent! time={}, src={}, dest={}, vc={}, seq_num={}", time, src, dest, vc, seq_num);
                    failed = true;
                }

                //This should never fail since seq_nums should be unique for a given src
                if let Some(last_time) = packet_sent_tracker.insert(
                    PacketInfo{src: *src, dest: *dest, vc: *vc, seq_num: *seq_num},
                    *time
                ) {
                    println!("Packet sent twice: last_time={}, new_time={}, src={}, dest={}, vc={}, seq_num={}",
                        last_time,
                        time,
                        src,
                        dest,
                        vc,
                        seq_num
                    );
                    failed = true;
                }
            },
            PacketOperation{time, operation: PacketOperationType::Received, info: PacketInfo{src, dest, vc, seq_num}} => {
                if let None = packet_sent_tracker.remove(&PacketInfo{src: *src, dest: *dest, vc: *vc, seq_num: *seq_num}) {
                    println!("Packet received but not yet sent: time={}, src={}, dest={}, vc={}, seq_num={}", time, src, dest, vc, seq_num);
                    failed = true;
                }
            },
        }
    }

    if !packet_sent_tracker.is_empty() {
        println!("There were {} packet(s) sent but not received:", packet_sent_tracker.len());
        for (PacketInfo{src, dest, vc, seq_num}, time) in packet_sent_tracker.into_iter() {
            println!("Packet sent but never received: time={}, src={}, dest={}, vc={}, seq_num={}", time, src, dest, vc, seq_num);
        }
        failed = true;
    }

    if failed {
        Err("verif_client_check.rs failed routing and connectivity check.".to_string())
    } else {
        println!("Routing and connectivity check succeeded!");
        Ok(())
    }
}

fn check_inorderness(n_value: usize, vc_w_value: usize, operations: &[PacketOperation]) -> Result<(), String> {
    println!("Performing in-order-ness check...");
    check_sent_in_order(n_value, vc_w_value, operations)?;
    check_received_in_order(n_value, vc_w_value, operations)?;
    println!("In-order-ness check succeeded!");
    Ok(())
}

fn check_sent_in_order(n_value: usize, vc_w_value: usize, operations: &[PacketOperation]) -> Result<(), String> {
    //Check that all sent packets had monotonically increasing sequence numbers within a given sender and VC
    //TODO make this 2D array more efficient than a bunch of boxes in a box
    let mut sent_packets_by_src: Box<[Box<[Vec<(u64, PacketInfo)>]>]>
        = make_array(n_value, make_array(vc_w_value, Vec::new()));

    let mut failed = false;

    for operation in operations {
        if let PacketOperation{time, operation: PacketOperationType::Sent, info: PacketInfo{src, dest, vc, seq_num}} = operation {
            let vec_of_interest = &mut sent_packets_by_src[*src as usize][*vc as usize];

            //Ensure the sequence numbers are monotonically increasing
            //We could sometimes skip sequence numbers (ex. due to weirdness at reset)
            //This is okay because it's another test's responsibility to ensure no _actually sent_
            //packets have been lost
            if let Some(
                (last_time, PacketInfo{src: last_src, dest: last_dest, vc: last_vc, seq_num: last_seq_num})
            ) = vec_of_interest.last() {
                assert!(last_time <= time);//operations should be sorted by time
                assert!(last_src == src);//Otherwise why was it placed in the array at this index?
                if last_seq_num >= seq_num {
                    println!("Packet from src={} sent out of order: last_time={}, last_dest={}, last_vc={}, last_seq_num={}, new_time={}, new_dest={}, new_vc={}, new_seq_num={}",
                        src,
                        last_time,
                        last_dest,
                        last_vc,
                        last_seq_num,
                        time,
                        dest,
                        vc,
                        seq_num
                    );

                    failed = true;
                }
            }

            //Keep going!
            vec_of_interest.push((*time, PacketInfo{src: *src, dest: *dest, vc: *vc, seq_num: *seq_num}));
        }
    }

    //Made it!
    if failed {
        Err("verif_client sent-in-order-ness check failed.".to_string())
    } else {
        Ok(())
    }
}

fn check_received_in_order(n_value: usize, vc_w_value: usize, operations: &[PacketOperation]) -> Result<(), String> {
    //Check that all sent packets had monotonically increasing sequence numbers within a given destination-sender combination
    //First index is the destination, second index is the source, and the Vec contains received packets in order of time
    //TODO make this array more efficient than a bunch of boxes in a box
    let mut received_packets_by_dest_and_src: Box<[Box<[Box<[Vec<(u64, PacketInfo)>]>]>]>
        = make_array(n_value as usize, make_array(n_value as usize, make_array(vc_w_value, Vec::new())));

    let mut failed = false;

    for operation in operations {
        if let PacketOperation{time, operation: PacketOperationType::Received, info: PacketInfo{src, dest, vc, seq_num}} = operation {
            let vec_of_interest = &mut received_packets_by_dest_and_src[*dest as usize][*src as usize][*vc as usize];

            //Ensure the sequence numbers are monotonically increasing
            //Sequence numbers could be skipped due to weirdness at reset, or due to a sender
            //sending to a different receiver. But they must be increasing!
            if let Some(
                (last_time, PacketInfo{src: last_src, dest: last_dest, vc: last_vc, seq_num: last_seq_num})
            ) = vec_of_interest.last() {
                assert!(last_time <= time);//Operations should be sorted by time
                assert!(last_dest == dest);//Otherwise why was it placed in the array at this index?
                assert!(last_src  == src);//Otherwise why was it placed in the array at this index?
                if last_seq_num >= seq_num {
                    println!("Packet set by src={} to dest={} received out of order: last_time={}, last_vc={}, last_seq_num={}, new_time={}, new_vc={}, new_seq_num={}",
                        src,
                        dest,
                        last_time,
                        last_vc,
                        last_seq_num,
                        time,
                        vc,
                        seq_num
                    );

                    failed = true;
                }
            }

            //Keep going!
            vec_of_interest.push((*time, PacketInfo{src: *src, dest: *dest, vc: *vc, seq_num: *seq_num}));
        }
    }

    //Made it!
    if failed {
        Err("verif_client received-in-order-ness check failed.".to_string())
    } else {
        Ok(())
    }
}


/* ------------------------------------------------------------------------------------------------
 * Tests
 * --------------------------------------------------------------------------------------------- */

#[cfg(test)]
mod tests {
    //use super::*;

    //TODO more tests
}

/* ------------------------------------------------------------------------------------------------
 * Benchmarks
 * --------------------------------------------------------------------------------------------- */

//TODO
