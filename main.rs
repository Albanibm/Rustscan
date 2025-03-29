//! Bitcoin Key Hunter - Optimized for Apple M1/M-Series Chips
//! A high-performance implementation for Bitcoin private key hunting

// --- Dependencies ---
use bs58;
use clap::{Parser, Subcommand};
use color_eyre::eyre::{eyre, Result, WrapErr};
use crossbeam::channel::{bounded, Receiver, Sender};
use hex;
use num_bigint::{BigUint, ToBigUint};
use once_cell::sync::Lazy;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use ripemd::{Digest as RipemdDigest, Ripemd160};
use secp256k1::{PublicKey, Secp256k1, SecretKey};
use sha2::Sha256;
use std::cell::RefCell;
use std::fmt::Write as FmtWrite;
use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

// --- Constants ---
const BATCH_SIZE: usize = 1024;  // Increased batch size for better throughput
const ADDRESS_PREFIX: u8 = 0x00;
const TARGET_HASH160_LEN: usize = 20;

// SECP256k1 context, pre-allocated for efficiency
static SECP: Lazy<Secp256k1<secp256k1::All>> = Lazy::new(Secp256k1::new);

// SECP256k1 curve order N
static SECP256K1_ORDER: Lazy<BigUint> = Lazy::new(|| {
    BigUint::parse_bytes(
        b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
        16,
    )
    .expect("Failed to parse SECP256K1_ORDER constant")
});

// Thread-local resources
thread_local! {
    static THREAD_RNG: RefCell<ChaCha20Rng> = RefCell::new(ChaCha20Rng::from_entropy());
    static SHA256_HASHER: RefCell<Sha256> = RefCell::new(Sha256::new());
    static RIPEMD160_HASHER: RefCell<Ripemd160> = RefCell::new(Ripemd160::new());
}

// Global counters
static KEYS_GENERATED: AtomicU64 = AtomicU64::new(0);
static MIN_PRIVATE_KEY: Lazy<BigUint> = Lazy::new(|| 1u8.to_biguint().unwrap());
static MAX_PRIVATE_KEY: Lazy<BigUint> = Lazy::new(|| &*SECP256K1_ORDER - 1u8);

// --- CLI Definitions ---
#[derive(Parser, Debug)]
#[command(author, version, about = "High-Performance Bitcoin Private Key Hunter (M1 Optimized)")]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    Search {
        #[arg(short, long)]
        address: String,
        #[arg(short = 's', long)]
        range_start: String,
        #[arg(short = 'e', long)]
        range_end: String,
        #[arg(short, long, default_value_t = num_cpus::get())]
        threads: usize,
        #[arg(short, long)]
        output: Option<String>,
        #[arg(long)]
        metrics: bool,
        #[arg(long)]
        sequential: bool,
    },
    Verify {
        #[arg(short, long)]
        thorough: bool,
    },
    Benchmark {
        #[arg(short, long, default_value_t = 10)]
        duration: u64,
        #[arg(short, long)]
        threads: Option<usize>,
    },
}

// --- Core Functions ---
#[inline]
fn derive_pubkey_hash(private_key: &[u8; 32]) -> Result<[u8; TARGET_HASH160_LEN]> {
    let secret_key = SecretKey::from_slice(private_key)?;
    let public_key = PublicKey::from_secret_key(&SECP, &secret_key);
    let public_key_bytes = public_key.serialize();

    SHA256_HASHER.with(|hasher| {
        let mut hasher = hasher.borrow_mut();
        hasher.update(&public_key_bytes);
        let sha256_result = hasher.finalize_reset();

        RIPEMD160_HASHER.with(|hasher| {
            let mut hasher = hasher.borrow_mut();
            hasher.update(&sha256_result);
            Ok(hasher.finalize_reset().into())
        })
    })
}

// --- In hash160_to_address function ---
fn hash160_to_address(hash160: &[u8; TARGET_HASH160_LEN]) -> String {
    let mut address_bytes = Vec::with_capacity(25);
    address_bytes.push(ADDRESS_PREFIX);
    address_bytes.extend_from_slice(hash160);

    let checksum: [u8; 4] = SHA256_HASHER.with(|hasher| {
        let mut hasher = hasher.borrow_mut();
        hasher.update(&address_bytes);
        let hash1 = hasher.finalize_reset();
        hasher.update(&hash1);
        let hash2 = hasher.finalize_reset();
        let mut checksum = [0u8; 4];
        checksum.copy_from_slice(&hash2[..4]);
        checksum
    });

    address_bytes.extend_from_slice(&checksum);
    bs58::encode(&address_bytes).into_string()
}

// --- In decode_address_to_hash160 function ---
fn decode_address_to_hash160(address: &str) -> Result<[u8; TARGET_HASH160_LEN]> {
    let decoded = bs58::decode(address)
        .into_vec()
        .map_err(|e| eyre!("Invalid base58: {}", e))?;

    if decoded.len() != 25 {
        return Err(eyre!("Invalid address length: {} bytes", decoded.len()));
    }

    if decoded[0] != ADDRESS_PREFIX {
        return Err(eyre!("Invalid version byte: {}", decoded[0]));
    }

    let (data, checksum) = decoded.split_at(21);
    let calculated_checksum: [u8; 4] = SHA256_HASHER.with(|hasher| {
        let mut hasher = hasher.borrow_mut();
        hasher.update(data);
        let hash1 = hasher.finalize_reset();
        hasher.update(&hash1);
        let hash2 = hasher.finalize_reset();
        let mut checksum = [0u8; 4];
        checksum.copy_from_slice(&hash2[..4]);
        checksum
    });

    if checksum != calculated_checksum {
        return Err(eyre!("Checksum mismatch"));
    }

    let mut hash160 = [0u8; 20];
    hash160.copy_from_slice(&data[1..]);
    Ok(hash160)
}
#[inline(always)]
fn hashes_match(h1: &[u8; TARGET_HASH160_LEN], h2: &[u8; TARGET_HASH160_LEN]) -> bool {
    h1 == h2
}

// --- Key Generation ---
fn get_keys_generated() -> u64 {
    KEYS_GENERATED.load(Ordering::Relaxed)
}

fn reset_keys_generated() {
    KEYS_GENERATED.store(0, Ordering::Relaxed);
}

fn parse_hex_to_bigint(hex_str: &str) -> Result<BigUint> {
    let clean_hex = hex_str.trim_start_matches("0x");
    match BigUint::parse_bytes(clean_hex.as_bytes(), 16) {
        Some(num) if num == 0u8.to_biguint().unwrap() => Err(eyre!("Private key cannot be zero")),
        Some(num) if num >= *SECP256K1_ORDER => Err(eyre!("Private key exceeds curve order")),
        Some(num) => Ok(num),
        None => Err(eyre!("Invalid hex string")),
    }
}

fn bigint_to_key_bytes(num: &BigUint) -> [u8; 32] {
    let bytes = num.to_bytes_be();
    let mut key_bytes = [0u8; 32];
    let start = 32 - bytes.len();
    key_bytes[start..].copy_from_slice(&bytes);
    key_bytes
}

fn bytes_to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

fn generate_random_key(range_start: &BigUint, range_end: &BigUint) -> [u8; 32] {
    let key_value = THREAD_RNG.with(|rng| {
        let mut rng = rng.borrow_mut();
        loop {
            let num = if range_start == &*MIN_PRIVATE_KEY && range_end == &*MAX_PRIVATE_KEY {
                BigUint::from_bytes_be(&{
                    let mut bytes = [0u8; 32];
                    rng.fill(&mut bytes);
                    bytes
                })
            } else {
                let range_size = range_end - range_start + 1u8;
                let random_bytes = {
                    let mut bytes = [0u8; 32];
                    rng.fill(&mut bytes);
                    bytes
                };
                range_start + (BigUint::from_bytes_be(&random_bytes) % range_size)
            };

            if num > 0u8.to_biguint().unwrap() && num < *SECP256K1_ORDER {
                KEYS_GENERATED.fetch_add(1, Ordering::Relaxed);
                return num;
            }
        }
    });
    bigint_to_key_bytes(&key_value)
}

fn generate_random_keys_batch(range_start: &BigUint, range_end: &BigUint, batch_size: usize) -> Vec<[u8; 32]> {
    let mut keys = Vec::with_capacity(batch_size);
    for _ in 0..batch_size {
        keys.push(generate_random_key(range_start, range_end));
    }
    keys
}

fn generate_sequential_key(current: &BigUint) -> Option<[u8; 32]> {
    if current >= &*SECP256K1_ORDER || current == &0u8.to_biguint().unwrap() {
        None
    } else {
        KEYS_GENERATED.fetch_add(1, Ordering::Relaxed);
        Some(bigint_to_key_bytes(current))
    }
}

fn key_from_hex(hex_string: &str) -> Result<[u8; 32]> {
    let clean_hex = hex_string.trim_start_matches("0x");
    let bytes = hex::decode(clean_hex).wrap_err("Invalid hex")?;
    if bytes.len() > 32 {
        return Err(eyre!("Key too long"));
    }

    let mut result = [0u8; 32];
    result[32 - bytes.len()..].copy_from_slice(&bytes);
    let key_int = BigUint::from_bytes_be(&result);

    if key_int == 0u8.to_biguint().unwrap() {
        Err(eyre!("Key cannot be zero"))
    } else if key_int >= *SECP256K1_ORDER {
        Err(eyre!("Key exceeds curve order"))
    } else {
        Ok(result)
    }
}

// --- Search Types ---
struct SearchContext {
    target_hash160: [u8; TARGET_HASH160_LEN],
    range_start: Arc<BigUint>,
    range_end: Arc<BigUint>,
    enable_metrics: bool,
    sequential: bool,
    current_sequential_key: Arc<parking_lot::Mutex<BigUint>>,
}

enum SearchUpdate {
    Progress(u64),
    Found {
        private_key_hex: String,
        address: String,
    },
}

#[derive(Debug)]
struct BenchmarkResults {
    total_keys: u64,
    keys_per_second: f64,
    detailed_metrics: Option<DetailedMetrics>,
}

#[derive(Debug)]
struct DetailedMetrics {
    avg_key_generation_ns: f64,
    avg_address_derivation_ns: f64,
    avg_comparison_ns: f64,
}

// --- Search Implementation ---
fn run_search(
    config: SearchContext,
    tx: Sender<SearchUpdate>,
    running: Arc<AtomicBool>,
    found_flag: Arc<AtomicBool>,
) -> Result<()> {
    reset_keys_generated();
    let num_threads = rayon::current_num_threads();

    rayon::scope(|s| {
        for _ in 0..num_threads {
            let tx = tx.clone();
            let running = Arc::clone(&running);
            let found_flag = Arc::clone(&found_flag);
            let config = SearchContext {
                target_hash160: config.target_hash160,
                range_start: Arc::clone(&config.range_start),
                range_end: Arc::clone(&config.range_end),
                enable_metrics: config.enable_metrics,
                sequential: config.sequential,
                current_sequential_key: Arc::clone(&config.current_sequential_key),
            };

            s.spawn(move |_| {
                let mut local_keys = 0;
                let mut key_gen_time = Duration::ZERO;
                let mut addr_time = Duration::ZERO;
                let mut cmp_time = Duration::ZERO;
                let mut last_report = Instant::now();

                'search: loop {
                    if !running.load(Ordering::Relaxed) || found_flag.load(Ordering::Relaxed) {
                        break 'search;
                    }

                    let keys = if config.sequential {
                        let mut keys = Vec::with_capacity(BATCH_SIZE);
                        let mut current = config.current_sequential_key.lock();
                        for _ in 0..BATCH_SIZE {
                            if *current > *config.range_end {
                                break;
                            }
                            if let Some(key) = generate_sequential_key(&*current) {
                                keys.push(key);
                            }
                            *current += 1u8;
                        }
                        keys
                    } else {
                        let start = if config.enable_metrics { Instant::now() } else { Instant::now() };
                        let keys = generate_random_keys_batch(&config.range_start, &config.range_end, BATCH_SIZE);
                        if config.enable_metrics { key_gen_time += start.elapsed(); }
                        keys
                    };

                    if keys.is_empty() {
                        break 'search;
                    }

                    for key in keys {
                        if !running.load(Ordering::Relaxed) || found_flag.load(Ordering::Relaxed) {
                            break 'search;
                        }

                        let start = if config.enable_metrics { Instant::now() } else { Instant::now() };
                        match derive_pubkey_hash(&key) {
                            Ok(hash) => {
                                if config.enable_metrics { addr_time += start.elapsed(); }
                                let start = if config.enable_metrics { Instant::now() } else { Instant::now() };
                                if hashes_match(&hash, &config.target_hash160) {
                                    if config.enable_metrics { cmp_time += start.elapsed(); }
                                    if found_flag.compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed).is_ok() {
                                        let _ = tx.send(SearchUpdate::Found {
                                            private_key_hex: bytes_to_hex(&key),
                                            address: hash160_to_address(&hash),
                                        });
                                        running.store(false, Ordering::SeqCst);
                                    }
                                    break 'search;
                                }
                                if config.enable_metrics { cmp_time += start.elapsed(); }
                            }
                            Err(_) => continue,
                        }
                        local_keys += 1;
                    }

                    if config.enable_metrics && last_report.elapsed() > Duration::from_secs(10) {
                        println!(
                            "Thread Metrics - Keys: {}, KeyGen: {:.2}ns, AddrDeriv: {:.2}ns, Compare: {:.2}ns",
                            local_keys,
                            key_gen_time.as_nanos() as f64 / local_keys as f64,
                            addr_time.as_nanos() as f64 / local_keys as f64,
                            cmp_time.as_nanos() as f64 / local_keys as f64
                        );
                        last_report = Instant::now();
                    }
                }
            });
        }
    });

    let _ = tx.send(SearchUpdate::Progress(get_keys_generated()));
    Ok(())
}

fn status_reporter(
    rx: Receiver<SearchUpdate>,
    running: Arc<AtomicBool>,
    found_flag: Arc<AtomicBool>,
    sequential: bool,
    range_start: Arc<BigUint>,
    range_end: Arc<BigUint>,
    current_sequential_key: Arc<parking_lot::Mutex<BigUint>>,
) {
    let start = Instant::now();
    let mut last_time = start;
    let mut last_keys = 0;
    let mut total_keys = 0;
    let mut found = None;

    loop {
        match rx.recv_timeout(Duration::from_millis(500)) {
            Ok(SearchUpdate::Progress(keys)) => total_keys = keys,
            Ok(SearchUpdate::Found { private_key_hex, address }) => found = Some((private_key_hex, address)),
            Err(crossbeam::channel::RecvTimeoutError::Timeout) => total_keys = get_keys_generated(),
            Err(crossbeam::channel::RecvTimeoutError::Disconnected) => break,
        }

        if !running.load(Ordering::Relaxed) || found_flag.load(Ordering::Relaxed) || found.is_some() {
            total_keys = get_keys_generated();
            print!("\r\x1b[K");

            if let Some((key, addr)) = found {
                println!("MATCH FOUND!");
                println!("Private Key: {}", key);
                println!("Address: {}", addr);
            }

            println!("Final keys checked: {}", total_keys);
            let elapsed = start.elapsed().as_secs_f64();
            if elapsed > 0.0 {
                println!("Time: {:.2}s, Rate: {:.0} keys/s", elapsed, total_keys as f64 / elapsed);
            }
            break;
        }

        let now = Instant::now();
        let elapsed = now.duration_since(last_time).as_secs_f64();
        let keys_diff = total_keys - last_keys;
        let rate = if elapsed > 1e-9 { keys_diff as f64 / elapsed } else { 0.0 };

        print!("\r\x1b[K");
        if sequential {
            let current = current_sequential_key.lock().clone();
            let range_size = &*range_end - &*range_start + 1u8;
            let progress = &current - &*range_start;
            let percent = (&progress * 100u32) / &range_size;

            print!(
                "Seq Search: Key {}/{} ({}%) | Rate: {:.0} keys/s | Total: {}",
                current, *range_end, percent, rate, total_keys
            );
        } else {
            print!("Rand Search: {:.0} keys/s | Total: {}", rate, total_keys);
        }
        let _ = std::io::stdout().flush();

        last_keys = total_keys;
        last_time = now;
    }
}

// --- Benchmark Implementation ---
fn run_benchmark(duration: Duration, thread_count: usize) -> Result<BenchmarkResults> {
    reset_keys_generated();
    let running = Arc::new(AtomicBool::new(true));
    let stop_time = Instant::now() + duration;

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(thread_count)
        .build()
        .wrap_err("Failed to build thread pool")?;

    let key_gen_time = AtomicU64::new(0);
    let addr_time = AtomicU64::new(0);
    let cmp_time = AtomicU64::new(0);
    let target_hash = [0u8; 20];
    let range_start = Arc::new(MIN_PRIVATE_KEY.clone());
    let range_end = Arc::new(MAX_PRIVATE_KEY.clone());

    pool.scope(|s| {
        for _ in 0..thread_count {
            let running = Arc::clone(&running);
            let key_gen_time = &key_gen_time;
            let addr_time = &addr_time;
            let cmp_time = &cmp_time;
            let range_start = Arc::clone(&range_start);
            let range_end = Arc::clone(&range_end);

            s.spawn(move |_| {
                while running.load(Ordering::Relaxed) && Instant::now() < stop_time {
                    let gen_start = Instant::now();
                    let keys = generate_random_keys_batch(&range_start, &range_end, BATCH_SIZE);
                    let gen_elapsed = gen_start.elapsed().as_nanos() as u64;
                    key_gen_time.fetch_add(gen_elapsed, Ordering::Relaxed);

                    let mut batch_addr_time = 0;
                    let mut batch_cmp_time = 0;

                    for key in keys {
                        if !running.load(Ordering::Relaxed) || Instant::now() >= stop_time {
                            break;
                        }

                        let start = Instant::now();
                        if let Ok(hash) = derive_pubkey_hash(&key) {
                            batch_addr_time += start.elapsed().as_nanos() as u64;
                            let start = Instant::now();
                            let _ = hashes_match(&hash, &target_hash);
                            batch_cmp_time += start.elapsed().as_nanos() as u64;
                        } else {
                            batch_addr_time += start.elapsed().as_nanos() as u64;
                        }
                    }

                    addr_time.fetch_add(batch_addr_time, Ordering::Relaxed);
                    cmp_time.fetch_add(batch_cmp_time, Ordering::Relaxed);
                }
            });
        }
    });

    running.store(false, Ordering::SeqCst);
    let total_keys = get_keys_generated();
    let elapsed = duration.as_secs_f64();
    let rate = if elapsed > 0.0 { total_keys as f64 / elapsed } else { 0.0 };

    let metrics = if total_keys > 0 {
        Some(DetailedMetrics {
            avg_key_generation_ns: key_gen_time.load(Ordering::Relaxed) as f64 / total_keys as f64,
            avg_address_derivation_ns: addr_time.load(Ordering::Relaxed) as f64 / total_keys as f64,
            avg_comparison_ns: cmp_time.load(Ordering::Relaxed) as f64 / total_keys as f64,
        })
    } else {
        None
    };

    Ok(BenchmarkResults {
        total_keys,
        keys_per_second: rate,
        detailed_metrics: metrics,
    })
}

// --- Verification ---
fn verify_key_address_pair(private_key_hex: &str, expected_address: &str) -> Result<()> {
    println!("Verifying Key: {}", private_key_hex);
    println!("Expected Addr: {}", expected_address);

    let start = Instant::now();
    let key_bytes = key_from_hex(private_key_hex)?;
    let derived_hash = derive_pubkey_hash(&key_bytes)?;
    let derived_address = hash160_to_address(&derived_hash);
    let elapsed = start.elapsed();

    println!("Derived Addr: {}", derived_address);
    println!("Time: {:?}", elapsed);

    if derived_address == expected_address {
        println!("✓ PASSED");
        Ok(())
    } else {
        println!("✗ FAILED");
        Err(eyre!("Address mismatch"))
    }
}

fn run_thorough_verification() -> Result<()> {
    println!("\n--- Thorough Verification ---");
    verify_key_address_pair(
        "00000000000000000000000000000000000000000000000000000000001ba534",
        "14oFNXucftsHiUMY8uctg6N487riuyXs4h",
    )?;
    println!("\n✓ All tests PASSED");
    Ok(())
}

// --- Main ---
fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::parse();

    let default_threads = num_cpus::get();
    let thread_count = match args.command {
        Command::Search { threads, .. } => threads,
        Command::Benchmark { threads, .. } => threads.unwrap_or(default_threads),
        Command::Verify { .. } => default_threads,
    };

    rayon::ThreadPoolBuilder::new()
        .num_threads(thread_count)
        .build_global()
        .wrap_err("Failed to initialize thread pool")?;

    println!("Using {} threads", thread_count);

    match args.command {
        Command::Search {
            address,
            range_start,
            range_end,
            threads,
            output: _,
            metrics,
            sequential,
        } => {
            println!("Target address: {}", address);
            let target_hash160 = decode_address_to_hash160(&address)?;
            println!("Target hash160: {}", bytes_to_hex(&target_hash160));

            let start_key = parse_hex_to_bigint(&range_start)?;
            let end_key = parse_hex_to_bigint(&range_end)?;

            if start_key > end_key {
                return Err(eyre!("Invalid range: start > end"));
            }

            println!("Mode: {}", if sequential { "Sequential" } else { "Random" });
            println!("Range:");
            println!("  Start: 0x{}", bytes_to_hex(&bigint_to_key_bytes(&start_key)));
            println!("  End:   0x{}", bytes_to_hex(&bigint_to_key_bytes(&end_key)));

            let running = Arc::new(AtomicBool::new(true));
            let found_flag = Arc::new(AtomicBool::new(false));
            let (tx, rx) = bounded(threads * 2);
            let current_key = Arc::new(parking_lot::Mutex::new(start_key.clone()));

            let context = SearchContext {
                target_hash160,
                range_start: Arc::new(start_key),
                range_end: Arc::new(end_key),
                enable_metrics: metrics,
                sequential,
                current_sequential_key: Arc::clone(&current_key),
            };

            let reporter = {
                let running = Arc::clone(&running);
                let found_flag = Arc::clone(&found_flag);
                let range_start = Arc::clone(&context.range_start);
                let range_end = Arc::clone(&context.range_end);
                let current_key = Arc::clone(&current_key);
                thread::spawn(move || {
                    status_reporter(rx, running, found_flag, sequential, range_start, range_end, current_key);
                })
            };

            let result = run_search(context, tx, Arc::clone(&running), Arc::clone(&found_flag));
            running.store(false, Ordering::SeqCst);
            reporter.join().unwrap();

            if let Err(e) = result {
                eprintln!("\nError: {}", e);
            }
        }
        Command::Verify { thorough } => {
            if thorough {
                run_thorough_verification()?;
            } else {
                verify_key_address_pair(
                    "00000000000000000000000000000000000000000000000000000000001ba534",
                    "14oFNXucftsHiUMY8uctg6N487riuyXs4h",
                )?;
            }
        }
        Command::Benchmark { duration, threads } => {
            let results = run_benchmark(Duration::from_secs(duration), threads.unwrap_or(default_threads))?;
            println!("\nBenchmark Results:");
            println!("  Total keys: {}", results.total_keys);
            println!("  Rate: {:.0} keys/s", results.keys_per_second);
            if let Some(metrics) = results.detailed_metrics {
                println!("  Key gen: {:.2} ns/key", metrics.avg_key_generation_ns);
                println!("  Addr deriv: {:.2} ns/key", metrics.avg_address_derivation_ns);
                println!("  Compare: {:.2} ns/key", metrics.avg_comparison_ns);
            }
        }
    }

    Ok(())
}
