/*
 * File:    parse.rs
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

//TODO REMOVE ME
#![allow(dead_code)]

/* ------------------------------------------------------------------------------------------------
 * Submodules
 * --------------------------------------------------------------------------------------------- */

//TODO (includes "mod ..." and "pub mod ...")

/* ------------------------------------------------------------------------------------------------
 * Uses
 * --------------------------------------------------------------------------------------------- */

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::str::SplitWhitespace;

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

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum VerifClientMessage {
    Info{
        time:       u64,
        n_value:    usize,
        vc_w_value: usize
    },
    Sent{
        time:   u64,
        src:    u32,
        dest:   u32,
        vc:     u32,
        data:   u128,
    },
    Received{
        time:   u64,
        dest:   u32,
        vc:     u32,
        data:   u128,
    },
    Done{
        time:       u64,
        pe:         u32,
        attempts:   u32,
        sent:       u32,
    },
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum TRouteMessage {
    Info{
        time:       u64,
        n_value:    usize,
        vc_w_value: usize
    },
    Transfer{
        posx:       u32,
        posl:       u32,
        vc:         u32,
        l_o_v:      bool,
        r_o_v:      bool,
        u0_o_v:     bool,
        l_sel:      u32,
        r_sel:      u32,
        u0_sel:     u32,
        l_i_addr:   u32,
        r_i_addr:   u32,
        u0_i_addr:  u32,
    },
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum PiRouteMessage {
    Info{
        time:       u64,
        n_value:    usize,
        vc_w_value: usize
    },
    Transfer{
        posx:       u32,
        posl:       u32,
        vc:         u32,
        l_o_v:      bool,
        r_o_v:      bool,
        u0_o_v:     bool,
        u1_o_v:     bool,
        l_sel:      u32,
        r_sel:      u32,
        u0_sel:     u32,
        u1_sel:     u32,
        l_i_addr:   u32,
        r_i_addr:   u32,
        u0_i_addr:  u32,
        u1_i_addr:  u32,
    },
}

#[derive(Debug)]
pub struct ParsedMessages {
    verif_client_messages:  Vec<VerifClientMessage>,
    t_route_messages:       Vec<TRouteMessage>,
    pi_route_messages:      Vec<PiRouteMessage>,
}

/* ------------------------------------------------------------------------------------------------
 * Associated Functions and Methods
 * --------------------------------------------------------------------------------------------- */

impl ParsedMessages {
    pub(crate) fn get_verif_client_messages(&self) -> &[VerifClientMessage] {
        &self.verif_client_messages
    }

    pub(crate) fn get_t_route_messages(&self) -> &[TRouteMessage] {
        &self.t_route_messages
    }

    pub(crate) fn get_pi_route_messages(&self) -> &[PiRouteMessage] {
        &self.pi_route_messages
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

pub fn parse_from_file(log_path: impl AsRef<Path>) -> Result<ParsedMessages, String> {
    println!("Opening log file: \"{}\"", log_path.as_ref().display());
    let file    = File::open(log_path).map_err(|e| format!("Error opening log file: {}", e))?;
    let reader  = BufReader::new(file);

    println!("Success! Parsing log file...");
    parse(reader)
}

//TODO make this private and expose a single parse method that does all types
pub fn parse(reader: impl BufRead) -> Result<ParsedMessages, String> {
    let mut verif_client_messages   = Vec::new();
    let t_route_messages        = Vec::new();
    let pi_route_messages       = Vec::new();

    for line in reader.lines() {
        let line = line.map_err(|e| format!("Failed to read line: {}", e))?;

        fn chew(remainder: &str) -> Result<(u64, SplitWhitespace), String> {
            let (time, remainder) = remainder.split_once(":").ok_or(format!("Bad syntax: \"{}\"", remainder))?;
            let time: u64 = time.parse().map_err(|e| format!("Failed to parse time: {}", e))?;
            let remainder = remainder.split_whitespace();
            Ok((time, remainder))
        }

        match line.split_once("@") {
            Some(("<verif_client>", remainder)) => {
                let (time, remainder) = chew(remainder)?;
                verif_client_messages.push(parse_verif_client_line(&line, time, remainder)?);
            },
            //Don't bother parsing these messages until we end up using them in the future for something
            /*
            Some(("<t_route>", remainder)) => {
                let (time, remainder) = chew(remainder)?;
                t_route_messages.push(parse_t_route_line(&line, time, remainder)?);
            },
            Some(("<pi_route>", remainder)) => {
                let (time, remainder) = chew(remainder)?;
                pi_route_messages.push(parse_pi_route_line(&line, time, remainder)?);
            },
            */
            _ => {}
        }
    }

    Ok(ParsedMessages {
        verif_client_messages,
        t_route_messages,
        pi_route_messages,
    })
}

fn parse_verif_client_line(line: &str, time: u64, mut remainder: SplitWhitespace) -> Result<VerifClientMessage, String> {
    let mut next = || remainder.next().ok_or(format!("Bad syntax: \"{}\"", line));
    match next() {
        Ok("Info:") => {
            Ok(VerifClientMessage::Info{
                time,
                n_value:    parse_equals(&next()?)?,
                vc_w_value: parse_equals(&next()?)?,
            })
        }
        Ok("Sent") => {
            Ok(VerifClientMessage::Sent{
                time,
                src:    parse_equals(&next()?)?,
                dest:   parse_equals(&next()?)?,
                vc:     parse_equals(&next()?)?,
                data:   parse_equals(&next()?)?,
            })
        },
        Ok("Received") => {
            Ok(VerifClientMessage::Received{
                time,
                dest:   parse_equals(&next()?)?,
                vc:     parse_equals(&next()?)?,
                data:   parse_equals(&next()?)?,
            })
        },
        Ok("Done") => {
            Ok(VerifClientMessage::Done{
                time,
                pe:         parse_equals(&next()?)?,
                attempts:   parse_equals(&next()?)?,
                sent:       parse_equals(&next()?)?,
            })
        },
        _ => Err(format!("Bad syntax: \"{}\"", line))
    }
}

fn parse_t_route_line(line: &str, time: u64, mut remainder: SplitWhitespace) -> Result<TRouteMessage, String> {
    let mut next = || remainder.next().ok_or(format!("Bad syntax: \"{}\"", line));
    match next() {
        Ok("Info:") => {
            Ok(TRouteMessage::Info{
                time,
                n_value:    parse_equals(&next()?)?,
                vc_w_value: parse_equals(&next()?)?,
            })
        }
        Ok(posx_str) => {
            Ok(TRouteMessage::Transfer {
                posx:       parse_equals(&posx_str)?,
                posl:       parse_equals(&next()?)?,
                vc:         parse_equals(&next()?)?,
                l_o_v:      parse_equals_bool(&next()?)?,
                r_o_v:      parse_equals_bool(&next()?)?,
                u0_o_v:     parse_equals_bool(&next()?)?,
                l_sel:      parse_equals(&next()?)?,
                r_sel:      parse_equals(&next()?)?,
                u0_sel:     parse_equals(&next()?)?,
                l_i_addr:   parse_equals(&next()?)?,
                r_i_addr:   parse_equals(&next()?)?,
                u0_i_addr:  parse_equals(&next()?)?,
            })
        },
        _ => Err(format!("Bad syntax: \"{}\"", line))
    }
}

fn parse_pi_route_line(line: &str, time: u64, mut remainder: SplitWhitespace) -> Result<PiRouteMessage, String> {
    let mut next = || remainder.next().ok_or(format!("Bad syntax: \"{}\"", line));
    match next() {
        Ok("Info:") => {
            Ok(PiRouteMessage::Info{
                time,
                n_value:    parse_equals(&next()?)?,
                vc_w_value: parse_equals(&next()?)?,
            })
        }
        Ok(posx_str) => {
            Ok(PiRouteMessage::Transfer {
                posx:       parse_equals(&posx_str)?,
                posl:       parse_equals(&next()?)?,
                vc:         parse_equals(&next()?)?,
                l_o_v:      parse_equals_bool(&next()?)?,
                r_o_v:      parse_equals_bool(&next()?)?,
                u0_o_v:     parse_equals_bool(&next()?)?,
                u1_o_v:     parse_equals_bool(&next()?)?,
                l_sel:      parse_equals(&next()?)?,
                r_sel:      parse_equals(&next()?)?,
                u0_sel:     parse_equals(&next()?)?,
                u1_sel:     parse_equals(&next()?)?,
                l_i_addr:   parse_equals(&next()?)?,
                r_i_addr:   parse_equals(&next()?)?,
                u0_i_addr:  parse_equals(&next()?)?,
                u1_i_addr:  parse_equals(&next()?)?,
            })
        },
        _ => Err(format!("Bad syntax: \"{}\"", line))
    }
}

fn parse_equals_bool(equals: &str) -> Result<bool, String> {
    let binary: u8 = parse_equals(equals)?;

    match binary {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(format!("Bad syntax: \"{}\"", equals))
    }
}

fn parse_equals<T: std::str::FromStr>(equals: &str) -> Result<T, String> {
    equals.split('=')
        .nth(1).ok_or(format!("Bad syntax: \"{}\"", equals))?
        .parse().map_err(|_| format!("Failed to parse: {}", equals))
}

/* ------------------------------------------------------------------------------------------------
 * Tests
 * --------------------------------------------------------------------------------------------- */

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanity_parse_equals() {
        assert_eq!(parse_equals("N=5"), Ok(5));
    }

    //TODO more tests
}

/* ------------------------------------------------------------------------------------------------
 * Benchmarks
 * --------------------------------------------------------------------------------------------- */

//TODO
