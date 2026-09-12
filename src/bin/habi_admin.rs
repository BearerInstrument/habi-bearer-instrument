//! Minimal CLI client for talking to a running habi_node's admin
//! listener. Sends one AdminMessage, prints the AdminReply, exits.
//!
//! Usage:
//!   habi_admin <admin_addr> link-up <peer>
//!   habi_admin <admin_addr> link-down <peer>
//!   habi_admin <admin_addr> propagate <peer>
//!   habi_admin <admin_addr> spend <bearer>
//!   habi_admin <admin_addr> status

use habi_core::wire::{AdminMessage, AdminReply};
use std::env;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: {} <admin_addr> <link-up|link-down|propagate|spend|status> [arg]", args[0]);
        std::process::exit(1);
    }
    let addr = &args[1];
    let cmd = &args[2];

    let msg = match cmd.as_str() {
        "link-up" => AdminMessage::LinkUp { peer: args.get(3).cloned().unwrap_or_default() },
        "link-down" => AdminMessage::LinkDown { peer: args.get(3).cloned().unwrap_or_default() },
        "propagate" => AdminMessage::Propagate { peer: args.get(3).cloned().unwrap_or_default() },
        "spend" => AdminMessage::SpendAt { bearer: args.get(3).cloned().unwrap_or_default() },
        "status" => AdminMessage::Status,
        "seed" => AdminMessage::Seed { bearer: args.get(3).cloned().unwrap_or_default() },
        "conversion-day" => AdminMessage::ConversionDay,
        other => {
            eprintln!("unknown command: {other}");
            std::process::exit(1);
        }
    };

    let mut stream = TcpStream::connect(addr).unwrap_or_else(|e| {
        eprintln!("failed to connect to {addr}: {e}");
        std::process::exit(1);
    });
    writeln!(stream, "{}", msg.encode()).unwrap();

    let mut reader = BufReader::new(&stream);
    let mut line = String::new();
    reader.read_line(&mut line).unwrap();

    match AdminReply::decode(&line) {
        Ok(AdminReply::Ok) => println!("OK"),
        Ok(AdminReply::Error { detail }) => println!("ERROR: {detail}"),
        Ok(AdminReply::StatusReport { node_id, ledger, spent, links }) => {
            println!("node_id: {node_id}");
            println!("ledger:  {ledger:?}");
            println!("spent:   {spent:?}");
            println!("links:   {links:?}");
        }
        Err(e) => println!("malformed reply: {e} (raw: {line:?})"),
    }
}
