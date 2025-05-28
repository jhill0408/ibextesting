/*
 * File:    stats.rs
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

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct VerifClientStats {
    n_value:                        usize,
    vc_w_value:                     usize,
    cycles:                         u64,//Cycles from the first send to the last receive
    packets_sent_by_vc:             Box<[u64]>,
    packets_received_by_vc:         Box<[u64]>,
    best_latency_by_vc:             Box<[u64]>,
    worst_latency_by_vc:            Box<[u64]>,
    packets_sent_by_client:         Box<[u64]>,
    packets_received_by_client:     Box<[u64]>,
    best_latency_by_client_src:     Box<[u64]>,
    best_latency_by_client_dest:    Box<[u64]>,
    worst_latency_by_client_src:    Box<[u64]>,
    worst_latency_by_client_dest:   Box<[u64]>,
    //TODO others
}

/* ------------------------------------------------------------------------------------------------
 * Associated Functions and Methods
 * --------------------------------------------------------------------------------------------- */

impl VerifClientStats {
    pub fn determine_from(packet_operations: &PacketOperations) -> Result<VerifClientStats, String> {
        Ok(VerifClientStats {
            n_value:                        packet_operations.n_value,
            vc_w_value:                     packet_operations.vc_w_value,
            cycles:                         determine_cycles(packet_operations),
            packets_sent_by_vc:             determine_sent_by_vc(packet_operations),
            packets_received_by_vc:         determine_received_by_vc(packet_operations),
            best_latency_by_vc:             determine_best_latency_by_vc(packet_operations),
            worst_latency_by_vc:            determine_worst_latency_by_vc(packet_operations),
            packets_sent_by_client:         determine_sent_by_client(packet_operations),
            packets_received_by_client:     determine_received_by_client(packet_operations),
            best_latency_by_client_src:     determine_best_latency_by_client_src(packet_operations),
            best_latency_by_client_dest:    determine_best_latency_by_client_dest(packet_operations),
            worst_latency_by_client_src:    determine_worst_latency_by_client_src(packet_operations),
            worst_latency_by_client_dest:   determine_worst_latency_by_client_dest(packet_operations),
        })
    }

    pub fn get_n_value(&self) -> usize {
        self.n_value
    }

    pub fn get_vc_w_value(&self) -> usize {
        self.vc_w_value
    }

    pub fn get_cycles(&self) -> u64 {
        self.cycles
    }

    pub fn get_total_packets_sent(&self) -> u64 {
        self.packets_sent_by_vc.iter().sum()
    }

    pub fn get_total_packets_received(&self) -> u64 {
        self.packets_received_by_vc.iter().sum()
    }

    pub fn get_packets_sent_by_vc(&self) -> &[u64] {
        &self.packets_sent_by_vc
    }

    pub fn get_packets_received_by_vc(&self) -> &[u64] {
        &self.packets_received_by_vc
    }

    pub fn get_best_latency(&self) -> u64 {
        *self.best_latency_by_vc.iter().max().unwrap()
    }

    pub fn get_worst_latency(&self) -> u64 {
        *self.worst_latency_by_vc.iter().max().unwrap()
    }

    pub fn get_best_latency_by_vc(&self) -> &[u64] {
        &self.best_latency_by_vc
    }

    pub fn get_worst_latency_by_vc(&self) -> &[u64] {
        &self.worst_latency_by_vc
    }

    pub fn get_packets_sent_by_client(&self) -> &[u64] {
        &self.packets_sent_by_client
    }

    pub fn get_packets_received_by_client(&self) -> &[u64] {
        &self.packets_received_by_client
    }

    pub fn get_best_latency_by_client_src(&self) -> &[u64] {
        &self.best_latency_by_client_src
    }

    pub fn get_best_latency_by_client_dest(&self) -> &[u64] {
        &self.best_latency_by_client_dest
    }

    pub fn get_worst_latency_by_client_src(&self) -> &[u64] {
        &self.worst_latency_by_client_src
    }

    pub fn get_worst_latency_by_client_dest(&self) -> &[u64] {
        &self.worst_latency_by_client_dest
    }

    //TODO more granular statistics like by client, to client, and to vc all in different array dimensions

    //TODO in order to get switching activity, we need to add additional printouts to t_route and
    //pi_route and then parse those too

    pub fn get_noc_sustained_rate(&self) -> f64 {
        let total_packets_sent      = self.get_total_packets_sent() as f64;
        let cycles_taken            = self.get_cycles() as f64;
        let n_value                 = self.get_n_value() as f64;

        //Same formula that the original repo used
        total_packets_sent / (cycles_taken * n_value)
    }
}

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

fn determine_cycles(packet_operations: &PacketOperations) -> u64 {
    let mut earliest_time   = 0;
    let mut last_time       = 0;
    for operation in &packet_operations.operations {
        earliest_time   = earliest_time.min(operation.time);
        last_time       = last_time.max(operation.time);
    }

    last_time - earliest_time
}

fn determine_sent_by_vc(packet_operations: &PacketOperations) -> Box<[u64]> {
    let mut sent_by_vc = make_array(packet_operations.vc_w_value, 0);
    for operation in &packet_operations.operations {
        if let PacketOperation{operation: PacketOperationType::Sent, info: PacketInfo{vc, ..}, ..} = operation {
            sent_by_vc[*vc as usize] += 1;
        }
    }
    sent_by_vc
}

fn determine_received_by_vc(packet_operations: &PacketOperations) -> Box<[u64]> {
    let mut received_by_vc = make_array(packet_operations.vc_w_value, 0);
    for operation in &packet_operations.operations {
        if let PacketOperation{operation: PacketOperationType::Received, info: PacketInfo{vc, ..}, ..} = operation {
            received_by_vc[*vc as usize] += 1;
        }
    }
    received_by_vc
}

fn determine_best_worst_latency_by_vc(packet_operations: &PacketOperations) -> (Box<[u64]>, Box<[u64]>) {
    //Maps to the time the packet was sent
    let mut packet_sent_tracker: HashMap<&PacketInfo, u64>  = HashMap::new();

    let mut best_latency_by_vc                              = make_array(packet_operations.vc_w_value, u64::MAX);
    let mut worst_latency_by_vc                             = make_array(packet_operations.vc_w_value, 0);

    for operation in &packet_operations.operations {
        match operation {
            PacketOperation{time, operation: PacketOperationType::Sent, info} => {
                packet_sent_tracker.insert(info, *time);
            },
            PacketOperation{time, operation: PacketOperationType::Received, info} => {
                let corresponding_sent_time = packet_sent_tracker.remove(info).unwrap();

                let latency = time - corresponding_sent_time;

                best_latency_by_vc[info.vc as usize]    = best_latency_by_vc[info.vc as usize].min(latency);
                worst_latency_by_vc[info.vc as usize]   = worst_latency_by_vc[info.vc as usize].max(latency);
            },
        }
    }

    (best_latency_by_vc, worst_latency_by_vc)
}

fn determine_best_latency_by_vc(packet_operations: &PacketOperations) -> Box<[u64]> {
    determine_best_worst_latency_by_vc(packet_operations).0
}

fn determine_worst_latency_by_vc(packet_operations: &PacketOperations) -> Box<[u64]> {
    determine_best_worst_latency_by_vc(packet_operations).1
}

fn determine_sent_by_client(packet_operations: &PacketOperations) -> Box<[u64]> {
    let mut sent_by_client = make_array(packet_operations.n_value, 0);
    for operation in &packet_operations.operations {
        if let PacketOperation{operation: PacketOperationType::Sent, info: PacketInfo{src, ..}, ..} = operation {
            sent_by_client[*src as usize] += 1;
        }
    }
    sent_by_client
}

fn determine_received_by_client(packet_operations: &PacketOperations) -> Box<[u64]> {
    let mut received_by_client = make_array(packet_operations.n_value, 0);
    for operation in &packet_operations.operations {
        if let PacketOperation{operation: PacketOperationType::Received, info: PacketInfo{dest, ..}, ..} = operation {
            received_by_client[*dest as usize] += 1;
        }
    }
    received_by_client
}

fn get_best_worst_latency_by_client_src_dest(packet_operations: &PacketOperations) -> (Box<[u64]>, Box<[u64]>, Box<[u64]>, Box<[u64]>) {
    //Maps to the time the packet was sent
    let mut packet_sent_tracker: HashMap<&PacketInfo, u64>  = HashMap::new();

    let mut best_latency_by_client_src      = make_array(packet_operations.n_value, u64::MAX);
    let mut worst_latency_by_client_src     = make_array(packet_operations.n_value, 0);
    let mut worst_latency_by_client_dest    = make_array(packet_operations.n_value, 0);
    let mut best_latency_by_client_dest     = make_array(packet_operations.n_value, u64::MAX);

    for operation in &packet_operations.operations {
        match operation {
            PacketOperation{time, operation: PacketOperationType::Sent, info} => {
                packet_sent_tracker.insert(info, *time);
            },
            PacketOperation{time, operation: PacketOperationType::Received, info} => {
                let corresponding_sent_time = packet_sent_tracker.remove(info).unwrap();

                let latency = time - corresponding_sent_time;

                best_latency_by_client_src[info.src as usize]       = best_latency_by_client_src[info.src as usize].min(latency);
                worst_latency_by_client_src[info.src as usize]      = worst_latency_by_client_src[info.src as usize].max(latency);
                best_latency_by_client_dest[info.dest as usize]     = best_latency_by_client_dest[info.dest as usize].min(latency);
                worst_latency_by_client_dest[info.dest as usize]    = worst_latency_by_client_dest[info.dest as usize].max(latency);
            },
        }
    }

    (best_latency_by_client_src, worst_latency_by_client_src, best_latency_by_client_dest, worst_latency_by_client_dest)
}

fn determine_best_latency_by_client_src(packet_operations: &PacketOperations) -> Box<[u64]> {
    get_best_worst_latency_by_client_src_dest(packet_operations).0
}

fn determine_worst_latency_by_client_src(packet_operations: &PacketOperations) -> Box<[u64]> {
    get_best_worst_latency_by_client_src_dest(packet_operations).1
}

fn determine_best_latency_by_client_dest(packet_operations: &PacketOperations) -> Box<[u64]> {
    get_best_worst_latency_by_client_src_dest(packet_operations).2
}

fn determine_worst_latency_by_client_dest(packet_operations: &PacketOperations) -> Box<[u64]> {
    get_best_worst_latency_by_client_src_dest(packet_operations).3
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
