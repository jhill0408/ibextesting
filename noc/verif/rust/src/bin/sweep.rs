/*
 * File:    sweep.rs
 * Brief:   TODO
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

use std::path::{PathBuf, Path};
use std::process::*;
use std::fs::*;
use std::os::unix::fs::symlink;
use std::sync::Mutex;

/* ------------------------------------------------------------------------------------------------
 * Macros
 * --------------------------------------------------------------------------------------------- */

//TODO (also pub(crate) use the_macro statements here too)

/* ------------------------------------------------------------------------------------------------
 * Constants
 * --------------------------------------------------------------------------------------------- */

const THREADS_PER_SIM: usize = 1;//In testing Verilator doesn't scale well with multiple threads

const REL_OUTPUT_DIR:   &str = "results/sweep";
const REL_RTL_DIR:      &str = "rtl";
const REL_VERIF_DIR:    &str = "verif";
const REL_UNIT_DIR:     &str = "scripts/unit";

const REL_VERILATOR_WRAPPER: &str = "unit_verilator_wrapper.cpp";

//Compile time configs
const NAMES:                [&str; 3] = [
    "topology_t_binary_tree_sweep",
    "topology_pi_rectangle_sweep",
    "topology_pi_rectangle_generalized_sweep"
];
const N_VALS:               [u32; 6] = [2, 4, 8, 16, 32, 64];
const DW_VALS:              [u32; 1] = [32];
//TODO support VC_W=1
const VC_W_VALS:            [u32; 5] = [2, 3, 4, 8, 16];
const VC_FIFO_DEPTH_VALS:   [u32; 3] = [32, 64, 128];

//Runtime configs
//FIXME verif_client may be broken for the RATE=100 and/or BP_RATE=50 case
const RATES:                [u32; 20] = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100];
const BP_RATES:             [u32; 11] = [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50];

/* ------------------------------------------------------------------------------------------------
 * Static Variables
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Types
 * --------------------------------------------------------------------------------------------- */

struct Dirs {
    root:   PathBuf,
    output: PathBuf,
    rtl:    PathBuf,
    verif:  PathBuf,
    unit:   PathBuf,
}

#[derive(Debug)]
struct CompileConfig {
    name:           &'static str,
    n:              u32,
    dw:             u32,
    vc_w:           u32,
    vc_fifo_depth:  u32,
}

#[derive(Debug)]
struct RuntimeConfig {
    rate:       u32,
    bp_rate:    u32,
}

/* ------------------------------------------------------------------------------------------------
 * Associated Functions and Methods
 * --------------------------------------------------------------------------------------------- */

impl Dirs {
    fn output_dir_for_compile_config(&self, compile_config: &CompileConfig) -> PathBuf {
        let unique_name = format!(
            "{}_n{}_dw{}_vcw{}_vcfd{}_verilator_compile",
            compile_config.name,
            compile_config.n,
            compile_config.dw,
            compile_config.vc_w,
            compile_config.vc_fifo_depth
        );
        self.output.join(unique_name)
    }

    fn output_dir_for_runtime_config(&self, compile_config: &CompileConfig, runtime_config: &RuntimeConfig) -> PathBuf {
        let unique_name = format!(
            "{}_n{}_dw{}_vcw{}_vcfd{}_rate{}_bprate{}_verilator_run",
            compile_config.name,
            compile_config.n,
            compile_config.dw,
            compile_config.vc_w,
            compile_config.vc_fifo_depth,
            runtime_config.rate,
            runtime_config.bp_rate
        );
        self.output.join(unique_name)
    }

    fn get_wrapper_path(&self) -> PathBuf {
        self.unit.join(REL_VERILATOR_WRAPPER)
    }

    fn get_topologies_dir(&self) -> PathBuf {
        self.rtl.join("topologies")
    }

    fn get_verif_client_dir(&self) -> PathBuf {
        self.verif.join("client")
    }

    fn get_sweep_dir(&self) -> PathBuf {
        self.verif.join("sweep")
    }
    //TODO
}

/* ------------------------------------------------------------------------------------------------
 * Traits And Default Implementations
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Trait Implementations
 * --------------------------------------------------------------------------------------------- */

impl std::fmt::Display for CompileConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{{ name: {}, n: {}, dw: {}, vc_w: {}, vc_fifo_depth: {} }}", self.name, self.n, self.dw, self.vc_w, self.vc_fifo_depth)
    }
}

impl std::fmt::Display for RuntimeConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{{ rate: {}, bp_rate: {} }}", self.rate, self.bp_rate)
    }
}

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

fn main() -> Result<(), String> {
    let dirs = get_dirs();

    let compile_configs = generate_compile_configs();
    let runtime_configs = generate_runtime_configs();
    println!(
        "Sweeping {} compile config(s) across {} runtime config(s): Total of {} simulation(s)",
        compile_configs.len(),
        runtime_configs.len(),
        compile_configs.len() * runtime_configs.len()
    );

    //First run the compiles (these are parallelized by Verilator's Make invocation so we don't need to run more than one at a time)
    let mut job_queue: Vec<(&Dirs, &CompileConfig, &RuntimeConfig)> = Vec::new();
    for compile_config in compile_configs.iter() {
        println!("Compiling configuration: {}", compile_config);

        compile(&dirs, compile_config, THREADS_PER_SIM);

        for runtime_config in runtime_configs.iter() {
            job_queue.push((&dirs, compile_config, runtime_config));
        }
    }

    //The compiles themselves use all threads, but jobs don't since simulations don't scale that well with large numbers of threads
    //So instead we get parallelism by running multiple simulations at once!
    let num_simultaneous_sims = std::thread::available_parallelism().unwrap().get() / THREADS_PER_SIM;
    let job_queue: Mutex<Vec<(&Dirs, &CompileConfig, &RuntimeConfig)>> = std::sync::Mutex::new(job_queue);//Needs to be protected by a mutex now
    std::thread::scope(|s| {
        for _ in 0..num_simultaneous_sims {
            s.spawn(|| {
                simulation_management_thread(&job_queue);
            });
        }

        //All threads will be joined at the end of this closure's scope
    });

    Ok(())
}

fn simulation_management_thread(job_queue: &Mutex<Vec<(&Dirs, &CompileConfig, &RuntimeConfig)>>) {
    loop {
        let job = {
            let mut queue = job_queue.lock().unwrap();
            if queue.is_empty() {
                return;
            }
            queue.pop().unwrap()
        };

        println!("Running test with compile config: {} and runtime config: {}", job.1, job.2);

        run_test(job.0, job.1, job.2);
    }
}

fn get_dirs() -> Dirs {
    let repo_root = determine_repo_root();
    println!("Detected repo root as: \"{}\"", repo_root.display());

    let output_dir = repo_root.join(REL_OUTPUT_DIR);
    let _ = create_dir_all(&output_dir);
    let output_dir = output_dir.canonicalize().expect("Failed to canonicalize output dir");
    println!("Output dir:            \"{}\"", output_dir.display());

    let rtl_dir = repo_root.join(REL_RTL_DIR).canonicalize().expect("Failed to canonicalize rtl dir");
    println!("RTL dir:               \"{}\"", rtl_dir.display());

    let verif_dir = repo_root.join(REL_VERIF_DIR).canonicalize().expect("Failed to canonicalize verif dir");
    println!("Verif dir:             \"{}\"", verif_dir.display());

    let unit_dir = repo_root.join(REL_UNIT_DIR).canonicalize().expect("Failed to canonicalize unit dir");
    println!("Unit dir:              \"{}\"", unit_dir.display());

    Dirs {
        root:   repo_root,
        output: output_dir,
        rtl:    rtl_dir,
        verif:  verif_dir,
        unit:   unit_dir,
    }
}

fn determine_repo_root() -> PathBuf {
    let output = Command::new("git")
        .arg("rev-parse")
        .arg("--show-toplevel")
        .output()
        .expect("Failed to execute git command");

    if !output.status.success() {
        panic!("Failed to determine repo root");
    }

    let mut repo_root = String::from_utf8(output.stdout).expect("Failed to convert output to string");
    repo_root.truncate(repo_root.len() - 1);//Remove newline
    PathBuf::from(repo_root).canonicalize().expect("Failed to canonicalize repo root")
}

fn compile(dirs: &Dirs, compile_config: &CompileConfig, threads_per_sim: usize) {
    let output_dir = dirs.output_dir_for_compile_config(compile_config);
    let _ = remove_dir_all(&output_dir);
    let _ = create_dir_all(&output_dir);

    //Symlink helper
    let symlink_from_dir = |dir: &Path| {
        for entry in read_dir(&dir).expect("Failed to read rtl dir") {
            let entry       = entry.expect("Failed to read entry");
            let entry_path  = entry.path();
            let entry_name  = entry.file_name();
            let output_path = output_dir.join(entry_name);

            symlink(entry_path, output_path).expect("Failed to create symlink");
        }
    };

    //Simlink everything relevant
    symlink_from_dir(&dirs.rtl);
    symlink_from_dir(&dirs.get_topologies_dir());
    symlink(dirs.verif.join("verif_pkg.sv"), output_dir.join("verif_pkg.sv")).expect("Failed to create symlink");
    symlink_from_dir(&dirs.get_verif_client_dir());
    symlink_from_dir(&dirs.get_sweep_dir());
    symlink(dirs.get_wrapper_path(), output_dir.join(REL_VERILATOR_WRAPPER)).expect("Failed to create symlink");

    //Determine sources to compile
    //Note we filter out packages so they come first
    let all_sources: Vec<_> = read_dir(&output_dir).expect("Failed to read output dir")
        .map(|entry| entry.expect("Failed to read entry").file_name().to_string_lossy().to_string())
        .filter(|entry| entry.ends_with(".sv") || entry.ends_with(".v"))
        .collect();
    let pkg_sources: Vec<_> = all_sources.iter()
        .filter(|entry| entry.contains("_pkg.sv"))
        .collect();
    let non_pkg_sources: Vec<_> = all_sources.iter()
        .filter(|entry| !entry.contains("_pkg.sv"))
        .collect();

    //Run SV2V on the sources and output to a file
    let sv2v_output_file = File::create(output_dir.join("sv2v_verilator_sweep.sv")).expect("Failed to create sv2v output file");
    //sv2v $SOURCES -DVERILATOR -DREPO_ROOT=$REPO_ROOT -DSIMULATION --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=$TB > ${SV2V_OUTPUT}
    /*let sv2v_child = */Command::new("sv2v")
        .args(pkg_sources)
        .args(non_pkg_sources)
        .arg("-DVERILATOR")
        .arg("-DREPO_ROOT=".to_owned() + &dirs.root.to_string_lossy())
        .arg("-DSIMULATION")
        .arg("-DSWEEP_N=".to_owned() + &compile_config.n.to_string())
        .arg("-DSWEEP_D_W=".to_owned() + &compile_config.dw.to_string())
        .arg("-DSWEEP_VC_W=".to_owned() + &compile_config.vc_w.to_string())
        .arg("-DSWEEP_VC_FIFO_DEPTH=".to_owned() + &compile_config.vc_fifo_depth.to_string())
        .arg("--exclude=Always")
        .arg("--exclude=Assert")
        .arg("--exclude=UnbasedUnsized")
        .arg("--top=".to_owned() + compile_config.name)
        .stdout(sv2v_output_file)
        .current_dir(&output_dir)
        .spawn()
        .expect("Failed to spawn sv2v")
        .wait()
        .expect("Failed to wait for sv2v");

    //Run Verilator on the output of SV2V
    let compile_stdout_log = File::create(output_dir.join("verilator_compile_stdout.log")).expect("Failed to create compile log file");
    let compile_stderr_log = File::create(output_dir.join("verilator_compile_stderr.log")).expect("Failed to create compile log file");
    /*let verilator_output = */Command::new("verilator")
        .arg("--exe")
        .arg("--build")
        .arg("--timing")
        .arg("--build-jobs")
        .arg(std::thread::available_parallelism().unwrap().get().to_string())//Scales better than the sims do
        .arg("--threads")
        .arg(threads_per_sim.to_string())
        .arg("+1800-2012ext+sv")
        .arg("-sv")
        .arg("-Wall")
        .arg("-Wno-fatal")
        .arg("-cc")
        .arg("--assert")
        .arg("--top-module")
        .arg(compile_config.name)
        .arg("sv2v_verilator_sweep.sv")
        .arg("-CFLAGS")
        .arg("-fcoroutines")
        .arg("-CFLAGS")
        .arg("-DSV_TBENCH_NAME=".to_owned() + compile_config.name)
        .arg("-CFLAGS")
        .arg("-DVERILATED_CLASS=".to_owned() + "V" + compile_config.name)
        .arg("-CFLAGS")
        .arg("-DVERILATED_HEADER=".to_owned() + "\"V" + compile_config.name + ".h\"")
        .arg(output_dir.join(REL_VERILATOR_WRAPPER))
        .arg("-o")
        .arg(compile_config.name.to_owned() + ".elf")
        .current_dir(&output_dir)
        .stdout(compile_stdout_log)
        .stderr(compile_stderr_log)
        .spawn()
        .expect("Failed to spawn verilator")
        .wait()
        .expect("Failed to wait for verilator");
}

fn run_test(dirs: &Dirs, compile_config: &CompileConfig, runtime_config: &RuntimeConfig) {
    let compile_dir = dirs.output_dir_for_compile_config(compile_config);
    let output_dir  = dirs.output_dir_for_runtime_config(compile_config, runtime_config);
    let _ = remove_dir_all(&output_dir);
    let _ = create_dir_all(&output_dir);

    //Run the simulation
    let simulation_log = File::create(output_dir.join("verilation_simulation.log")).expect("Failed to create simulation log file");
    let test_child_status = Command::new(compile_dir.join("obj_dir").join(compile_config.name.to_owned() + ".elf"))
        .arg("+RATE=".to_owned() + &runtime_config.rate.to_string())
        .arg("+BP_RATE=".to_owned() + &runtime_config.bp_rate.to_string())
        .stdout(simulation_log)
        .current_dir(&output_dir)
        .spawn()
        .expect("Failed to spawn test")
        .wait()
        .expect("Failed to wait for test");

    //Check the exit status
    if !test_child_status.success() {
        println!("Error occured for compile config: {} and runtime config: {}", compile_config, runtime_config);
        panic!("Simulation failed with exit status: {}", test_child_status.code().unwrap());
    }

    //Run the checker on the log
    let checker_result = File::create(output_dir.join("check.txt")).expect("Failed to create checker result file");
    let checker_status = Command::new(dirs.verif.join("rust").join("target").join("release").join("log_checker"))
        .arg("verilation_simulation.log")
        .current_dir(&output_dir)
        .stdout(checker_result)
        .spawn()
        .expect("Failed to spawn checker")
        .wait()
        .expect("Failed to wait for checker");
    if !checker_status.success() {
        panic!("Checker failed with exit status: {}", checker_status.code().unwrap());
    }

    //Run stats collection
    let stats_txt = File::create(output_dir.join("results.txt")).expect("Failed to create stats file");
    let stats_status = Command::new(dirs.verif.join("rust").join("target").join("release").join("stats_from_log"))
        .arg("verilation_simulation.log")
        .arg("results.csv")
        .current_dir(&output_dir)
        .stdout(stats_txt)
        .spawn()
        .expect("Failed to spawn stats_from_log")
        .wait()
        .expect("Failed to wait for stats_from_log");
    if !stats_status.success() {
        panic!("Stats collection failed with exit status: {}", stats_status.code().unwrap());
    }
}

fn generate_compile_configs() -> Vec<CompileConfig> {
    let mut compile_configs = Vec::with_capacity(NAMES.len() * N_VALS.len() * DW_VALS.len() * VC_W_VALS.len() * VC_FIFO_DEPTH_VALS.len());
    for name in NAMES.iter() {
        for n in N_VALS.iter() {
            for dw in DW_VALS.iter() {
                for vc_w in VC_W_VALS.iter() {
                    for vc_fifo_depth in VC_FIFO_DEPTH_VALS.iter() {
                        compile_configs.push(CompileConfig {
                            name:           *name,
                            n:              *n,
                            dw:             *dw,
                            vc_w:           *vc_w,
                            vc_fifo_depth:  *vc_fifo_depth,
                        });
                    }
                }
            }
        }
    }

    compile_configs
}

fn generate_runtime_configs() -> Vec<RuntimeConfig> {
    let mut runtime_configs = Vec::with_capacity(RATES.len() * BP_RATES.len());
    for rate in RATES.iter() {
        for bp_rate in BP_RATES.iter() {
            runtime_configs.push(RuntimeConfig {
                rate:       *rate,
                bp_rate:    *bp_rate,
            });
        }
    }

    runtime_configs
}

/* ------------------------------------------------------------------------------------------------
 * Tests
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Benchmarks
 * --------------------------------------------------------------------------------------------- */

//TODO
