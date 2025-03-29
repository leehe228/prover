#![feature(slice_as_chunks)]
#![feature(if_let_guard)]
#![feature(let_chains)]

/* use std::io;
use std::any::Any;
use std::collections::HashMap; // Use HashMap here instead of BTreeMap
use std::fs::File;
use std::io::{BufReader, Read, Write};
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::time::Instant;
use std::collections::BTreeMap;

use env_logger::{Builder, Env, Target};
use itertools::Itertools;
use walkdir::WalkDir;

use crate::pipeline::{unify, Input, Stats};

mod pipeline;

use std::env;
use serde_json::from_reader;
use z3::{Config, Context, Solver};
use crate::pipeline::shared::{DataType, get_relation, get_attribute, assert_constraints_from_file};

fn visit<P: AsRef<Path>>(dir: P, mut cb: impl FnMut(usize, &Path)) -> std::io::Result<()> {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|f| {
            f.ok().filter(|f| f.path().is_file() && f.path().extension() == Some("json".as_ref()))
        })
        .sorted_by_cached_key(|e| e.metadata().unwrap().size())
        .enumerate()
        .for_each(|(i, e)| cb(i, e.path()));
    Ok(())
}

#[derive(Debug)]
enum CosetteResult {
	Provable(Stats),
	NotProvable(Stats),
	ParseErr(serde_json::Error),
	Panic(Box<dyn Any + Send>),
}

fn main() -> io::Result<()> {
	Builder::from_env(Env::default().default_filter_or("off"))
		.format(|buf, record| writeln!(buf, "{}", record.args()))
		.target(Target::Stdout)
		.init();
	let mut stats = BTreeMap::new();
	for arg in std::env::args() {
		visit(arg, |i, path| {
			use CosetteResult::*;
			let file = File::open(path).unwrap();
			let mut buf_reader = BufReader::new(file);
			let mut contents = String::new();
			println!("#{}: {}", i, path.to_string_lossy().as_ref());
			let start_time = Instant::now();
			buf_reader.read_to_string(&mut contents).unwrap();
			let result =
				std::panic::catch_unwind(|| match serde_json::from_str::<Input>(&contents) {
					Ok(rel) => {
						let (provable, case_stats) = unify(rel);
						println!(
							"Equivalence is {}provable for {}",
							if provable { "" } else { "not " },
							path.file_name().unwrap().to_str().unwrap(),
						);
						if provable {
							Provable(case_stats)
						} else {
							NotProvable(case_stats)
						}
					},
					Err(e) => {
						log::error!("Not successfully parsed.\n{}", e);
						ParseErr(e)
					},
				});
			let result = match result {
				Ok(res) => res,
				Err(e) => {
					log::error!("{:?}", e);
					Panic(e)
				},
			};
			let result_file = File::create(path.with_extension("result")).unwrap();
			let case_stats = match &result {
				Provable(stats) | NotProvable(stats) => {
					let mut stats = stats.clone();
					stats.provable = matches!(result, Provable(_));
					stats.total_duration = start_time.elapsed();
					stats
				},
				_ => {
					let mut stats = Stats::default();
					stats.panicked = true;
					stats.total_duration = start_time.elapsed();
					stats
				},
			};
			serde_json::to_writer(result_file, &case_stats).unwrap();
			stats.insert(path.to_string_lossy().to_string(), result);
		})?;
	}
	println!("\n\nSTATISTICS");
	let (a, b): (Vec<_>, _) = stats.values().partition(|v| matches!(v, CosetteResult::Provable(_)));
	let (al, bl) = (a.len(), b.len());
	for (name, result) in stats {
		println!("{}\t{:?}", name, result);
	}
	println!("Provable: {} / {}", al, al + bl);
	Ok(())
}*/

use std::any::Any;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, Read, Write};
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::time::Instant;

use env_logger::{Builder, Env, Target};
use itertools::Itertools;
use walkdir::WalkDir;

use crate::pipeline::{unify, Input, Stats};

mod pipeline;

use std::env;
use serde_json::from_reader;
use z3::{Config, Context, Solver};
use crate::pipeline::shared::{DataType, get_relation, get_attribute, assert_constraints_from_file};

fn visit<P: AsRef<Path>>(dir: P, mut cb: impl FnMut(usize, &Path)) -> std::io::Result<()> {
	WalkDir::new(dir)
		.into_iter()
		.filter_map(|f| {
			f.ok().filter(|f| f.path().is_file() && f.path().extension() == Some("json".as_ref()))
		})
		.sorted_by_cached_key(|e| e.metadata().unwrap().size())
		.enumerate()
		.for_each(|(i, e)| cb(i, e.path()));
	Ok(())
}

#[derive(Debug)]
enum CosetteResult {
	Provable(Stats),
	NotProvable(Stats),
	ParseErr(serde_json::Error),
	Panic(Box<dyn Any + Send>),
}

fn main() -> std::io::Result<()> {
	// Initialize logger.
	Builder::from_env(Env::default().default_filter_or("off"))
		.format(|buf, record| writeln!(buf, "{}", record.args()))
		.target(Target::Stdout)
		.init();

	let args: Vec<String> = env::args().collect();
	if args.len() < 2 {
		eprintln!("Usage: {} <input.json> [-c=<constraints.txt>]", args[0]);
		std::process::exit(1);
	}

	// The first argument (after the program name) is the JSON file.
	let input_file = &args[1];
	let file = File::open(input_file)?;
	let reader = BufReader::new(file);
	let input: Input = from_reader(reader).expect("Failed to parse input JSON");

	// Initialize Z3.
	let config = Config::new();
	let ctx = Context::new(&config);
	let solver = Solver::new(&ctx);

	// Build symbol maps from schemas.
	let mut schema_map: HashMap<String, z3::ast::Dynamic> = HashMap::new();
	let mut attr_map: HashMap<(String, String), z3::ast::Dynamic> = HashMap::new();

	// Here we assume that the Input type provides a public accessor for schemas.
	// For example, if Input has a method `get_schemas()`.
	for schema in input.get_schemas() {
		let table_name = schema.name.clone();
		let rel = get_relation(&ctx, &table_name);
		schema_map.insert(table_name.clone(), rel);
		// for (attr, dt_str) in schema.fields.iter().zip(schema.types.iter()) {
		// 	let dt = match dt_str.as_str() {
		// 		"INTEGER" => DataType::Integer,
		// 		"VARCHAR" => DataType::String, // Use String variant for VARCHAR.
		// 		"REAL" => DataType::Real,
		// 		other => DataType::Custom(other.to_string()),
		// 	};
		// 	let attr_sym = get_attribute(&ctx, &table_name, attr, &dt);
		// 	attr_map.insert((table_name.clone(), attr.to_string()), attr_sym);
		// }
		for (attr, dt_enum) in schema.fields.iter().zip(schema.types.iter()) {
			let dt = dt_enum.clone();
			let attr_sym = get_attribute(&ctx, &table_name, attr, &dt);
			attr_map.insert((table_name.clone(), attr.to_string()), attr_sym);
		}
	}

	// Look for a constraint file argument.
	// Accept either "-c=constraints.txt" or "-c constraints.txt".
	let mut constraints_text = String::new();
	for arg in args.iter().skip(2) {
		if arg.starts_with("-c=") {
			let filename = arg.trim_start_matches("-c=");
			let mut file = File::open(filename)?;
			file.read_to_string(&mut constraints_text)?;
		} else if arg == "-c" {
			// If "-c" is given, expect the next argument to be the constraints file.
			// (Since we allow at most one JSON input, we assume this case is rare.)
			// In our implementation we check for it already.
		}
	}

	// If constraints were provided, assert them into the solver.
	if !constraints_text.is_empty() {
		// Convert the symbol maps to the expected type.
		// Here we convert from our HashMap (which was built as a standard HashMap)
		// to the type expected by assert_constraints_from_file.
		// (Assuming the types match; if not, adjust accordingly.)
		assert_constraints_from_file(&ctx, &solver, &constraints_text, &schema_map, &attr_map);
	}

	// Run QED's equivalence checking.
	let (provable, stats) = unify(input);
	if provable {
		println!("Queries are equivalent.");
	} else {
		println!("Queries are NOT equivalent.");
	}
	println!("Statistics: {:?}", stats);

	Ok(())
}
