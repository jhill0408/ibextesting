/*
 * File:    stats_from_log.rs
 * Brief:   Parses a simulation log and determines various statistics
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
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

use noc_rs::parse::parse_from_file;
use noc_rs::verif_client::{self, VerifClientStats};

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

fn main() -> Result<(), String> {
    let mut args = std::env::args();
    if args.len() < 3 {
        println!("Usage: stats_from_log <log_file> <csv_output_file>");
        return Err("No log file provided as argument".to_string());
    }
    let messages = parse_from_file(args.nth(1).unwrap())?;

    println!("Looking for verif_client usage...");
    if let Some(packet_operations) = verif_client::interpret(&messages)? {
        let stats = VerifClientStats::determine_from(&packet_operations)?;
        write_human_readable(&stats, &mut std::io::stdout());

        let writer          = std::fs::File::create(args.next().unwrap()).map_err(|e| format!("Error opening csv file for writing: {}", e))?;
        let mut buffered    = std::io::BufWriter::new(writer);
        write_csv(&stats, &mut buffered);
    } else {
        println!("Didn't find verif_client messages in log, assuming it's not used in this test...");
    }

    println!("TODO in the future do stats based off of t_route and pi_route output too!");//TODO

    Ok(())
}

fn write_human_readable(stats: &VerifClientStats, writer: &mut impl std::io::Write) {
    writeln!(writer, "N                                 = {} client(s)",    stats.get_n_value()).unwrap();
    writeln!(writer, "VC_W                              = {} VC(s)",        stats.get_vc_w_value()).unwrap();
    writeln!(writer, "Cycles                            = {}",              stats.get_cycles()).unwrap();
    writeln!(writer, "Total packets sent                = {} packet(s)",    stats.get_total_packets_sent()).unwrap();
    writeln!(writer, "Total packets received            = {} packet(s)",    stats.get_total_packets_received()).unwrap();
    writeln!(writer, "Packets sent by VC                = {:?}",            stats.get_packets_sent_by_vc()).unwrap();
    writeln!(writer, "Packets received by VC            = {:?}",            stats.get_packets_received_by_vc()).unwrap();
    writeln!(writer, "Best latency overall              = {} cycle(s)",     stats.get_best_latency()).unwrap();
    writeln!(writer, "Worst latency overall             = {} cycle(s)",     stats.get_worst_latency()).unwrap();
    writeln!(writer, "Best latency by VC                = {:?}",            stats.get_best_latency_by_vc()).unwrap();
    writeln!(writer, "Worst latency by VC               = {:?}",            stats.get_worst_latency_by_vc()).unwrap();
    writeln!(writer, "Packets sent by client            = {:?}",            stats.get_packets_sent_by_client()).unwrap();
    writeln!(writer, "Packets received by client        = {:?}",            stats.get_packets_received_by_client()).unwrap();
    writeln!(writer, "Best latency by client src        = {:?}",            stats.get_best_latency_by_client_src()).unwrap();
    writeln!(writer, "Worst latency by client src       = {:?}",            stats.get_worst_latency_by_client_src()).unwrap();
    writeln!(writer, "Best latency by client dest       = {:?}",            stats.get_best_latency_by_client_dest()).unwrap();
    writeln!(writer, "Worst latency by client dest      = {:?}",            stats.get_worst_latency_by_client_dest()).unwrap();
    writeln!(writer, "NOC sustained rate                = {}%",             stats.get_noc_sustained_rate() * 99.0).unwrap();
    //TODO more stats
}

fn write_csv(stats: &VerifClientStats, writer: &mut impl std::io::Write) {
    //Header

    write!(writer, "N,VC_W,Cycles,Total_Packets_Sent,Total_Packets_Received,").unwrap();

    for i in 0..stats.get_vc_w_value() {
        write!(writer, "Packets_Sent_VC_{},", i).unwrap();
    }

    for i in 0..stats.get_vc_w_value() {
        write!(writer, "Packets_Received_VC_{},", i).unwrap();
    }

    write!(writer, "Best_Latency,Worst_Latency,").unwrap();

    for i in 0..stats.get_vc_w_value() {
        write!(writer, "Best_Latency_VC_{},", i).unwrap();
    }

    for i in 0..stats.get_vc_w_value() {
        write!(writer, "Worst_Latency_VC_{},", i).unwrap();
    }

    for i in 0..stats.get_n_value() {
        write!(writer, "Packets_Sent_Client_{},", i).unwrap();
    }

    for i in 0..stats.get_n_value() {
        write!(writer, "Packets_Received_Client_{},", i).unwrap();
    }

    for i in 0..stats.get_n_value() {
        write!(writer, "Best_Latency_Client_Src_{},", i).unwrap();
    }

    for i in 0..stats.get_n_value() {
        write!(writer, "Worst_Latency_Client_Src_{},", i).unwrap();
    }

    for i in 0..stats.get_n_value() {
        write!(writer, "Best_Latency_Client_Dest_{},", i).unwrap();
    }

    for i in 0..stats.get_n_value() {
        write!(writer, "Worst_Latency_Client_Dest_{},", i).unwrap();
    }

    writeln!(writer, "NOC_Sustained_Rate").unwrap();

    //Data

    write!(
        writer,
        "{},{},{},{},{},",
        stats.get_n_value(),
        stats.get_vc_w_value(),
        stats.get_cycles(),
        stats.get_total_packets_sent(),
        stats.get_total_packets_received(),
    ).unwrap();

    for packet_count in stats.get_packets_sent_by_vc() {
        write!(writer, "{},", packet_count).unwrap();
    }

    for packet_count in stats.get_packets_received_by_vc() {
        write!(writer, "{},", packet_count).unwrap();
    }

    write!(
        writer,
        "{},{},",
        stats.get_best_latency(),
        stats.get_worst_latency(),
    ).unwrap();

    for latency in stats.get_best_latency_by_vc() {
        write!(writer, "{},", latency).unwrap();
    }

    for latency in stats.get_worst_latency_by_vc() {
        write!(writer, "{},", latency).unwrap();
    }

    for packet_count in stats.get_packets_sent_by_client() {
        write!(writer, "{},", packet_count).unwrap();
    }

    for packet_count in stats.get_packets_received_by_client() {
        write!(writer, "{},", packet_count).unwrap();
    }

    for latency in stats.get_best_latency_by_client_src() {
        write!(writer, "{},", latency).unwrap();
    }

    for latency in stats.get_worst_latency_by_client_src() {
        write!(writer, "{},", latency).unwrap();
    }

    for latency in stats.get_best_latency_by_client_dest() {
        write!(writer, "{},", latency).unwrap();
    }

    for latency in stats.get_worst_latency_by_client_dest() {
        write!(writer, "{},", latency).unwrap();
    }

    writeln!(writer, "{}", stats.get_noc_sustained_rate()).unwrap();
}

/*
fn old_write_csv(stats: &VerifClientStats, writer: &mut impl std::io::Write) {
    let num_cols = 1 + stats.get_vc_w_value();

    fn write_single<T: std::fmt::Display>(writer: &mut impl std::io::Write, num_cols: usize, name: &str, single: T) {
        write!(writer, "{},{}", name, single).unwrap();
        for _ in 0..(num_cols - 2) {
            write!(writer, ",").unwrap();
        }
        writeln!(writer).unwrap();
    }

    fn write_slice<T: std::fmt::Display>(writer: &mut impl std::io::Write, name: &str, slice: &[T]) {
        write!(writer, "{}", name).unwrap();
        for item in slice {
            write!(writer, ",{}", item).unwrap();
        }
        writeln!(writer).unwrap();
    }

    write_single(writer, num_cols, "N",                         stats.get_n_value());
    write_single(writer, num_cols, "VC_W",                      stats.get_vc_w_value());
    write_single(writer, num_cols, "Cycles",                    stats.get_cycles());
    write_single(writer, num_cols, "Total packets sent",        stats.get_total_packets_sent());
    write_single(writer, num_cols, "Total packets received",    stats.get_total_packets_received());
    write_slice (writer,           "Packets sent by VC",        stats.get_packets_sent_by_vc());
    write_slice (writer,           "Packets received by VC",    stats.get_packets_received_by_vc());
    write_single(writer, num_cols, "Best latency overall",      stats.get_best_latency());
    write_single(writer, num_cols, "Worst latency overall",     stats.get_worst_latency());
    write_slice (writer,           "Best latency by VC",        stats.get_best_latency_by_vc());
    write_slice (writer,           "Worst latency by VC",       stats.get_worst_latency_by_vc());
    write_single(writer, num_cols, "NOC sustained rate",        stats.get_noc_sustained_rate());
    //TODO more stats
}
*/

/* ------------------------------------------------------------------------------------------------
 * Tests
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Benchmarks
 * --------------------------------------------------------------------------------------------- */

//TODO
