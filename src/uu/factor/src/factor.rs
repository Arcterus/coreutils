// * This file is part of the uutils coreutils package.
// *
// * (c) 2014 T. Jameson Little <t.jameson.little@gmail.com>
// * (c) 2020 nicoo <nicoo@debian.org>
// *
// * For the full copyright and license information, please view the LICENSE file
// * that was distributed with this source code.

extern crate rand;

#[macro_use]
extern crate uucore;

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BinaryHeap, VecDeque};
use std::error::Error;
use std::fmt;
use std::io::{self, stdin, stdout, BufRead, Write};
use std::ops;
use std::sync::mpsc;
use std::thread;

use rayon::prelude::*;

mod miller_rabin;
mod numeric;
mod rho;
mod table;

static SYNTAX: &str = "[OPTION] [NUMBER]...";
static SUMMARY: &str = "Print the prime factors of the given number(s).
 If none are specified, read from standard input.";
static LONG_HELP: &str = "";

struct Factors {
    //f: BTreeMap<u64, u8>,
    f: BinaryHeap<Reverse<(u64, u8)>>,
}

impl Factors {
    fn one() -> Factors {
        //Factors { f: BTreeMap::new() }
        Factors { f: BinaryHeap::new() }
    }

    fn prime(p: u64) -> Factors {
        debug_assert!(miller_rabin::is_prime(p));
        let mut f = Factors::one();
        f.push(p);
        f
    }

    fn add(&mut self, prime: u64, exp: u8) {
        debug_assert!(exp > 0);
        //let n = *self.f.get(&prime).unwrap_or(&0);
        //self.f.insert(prime, exp + n);
        self.f.push(Reverse((prime, exp)));
    }

    fn push(&mut self, prime: u64) {
        self.add(prime, 1)
    }

    #[cfg(test)]
    fn product(&self) -> u64 {
        self.f
            .iter()
            .fold(1, |acc, (p, exp)| acc * p.pow(*exp as u32))
    }
}

impl ops::MulAssign<Factors> for Factors {
    fn mul_assign(&mut self, other: Factors) {
        for Reverse((prime, exp)) in &other.f {
            self.add(*prime, *exp);
        }
    }
}

impl fmt::Display for Factors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for Reverse((p, exp)) in self.f.iter() {
            for _ in 0..*exp {
                write!(f, " {}", p)?
            }
        }

        Ok(())
    }
}

struct FactorStorage(usize, u64, Factors);

impl PartialEq for FactorStorage {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for FactorStorage { }

impl Ord for FactorStorage {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for FactorStorage {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn factor(mut n: u64) -> Factors {
    let mut factors = Factors::one();

    if n < 2 {
        factors.push(n);
        return factors;
    }

    let z = n.trailing_zeros();
    if z > 0 {
        factors.add(2, z as u8);
        n >>= z;
    }

    if n == 1 {
        return factors;
    }

    let (f, n) = table::factor(n);
    factors *= f;

    if n >= table::NEXT_PRIME {
        factors *= rho::factor(n);
    }

    factors
}

fn print_factors_str(num_str: &str, idx: usize, sender: &mut mpsc::Sender<Box<FactorStorage>>) -> Result<(), ()> {//Box<dyn Error>> {
    let res: Result<(), Box<dyn Error>> = num_str
        .parse::<u64>()
        .map_err(|e| e.into())
        .and_then(|x| sender.send(Box::new(FactorStorage(idx, x, factor(x)))).map_err(|e| e.into()));
    res.unwrap();
    Ok(())
}

fn process_elems(stdout: &mut impl io::Write, heap: &mut BinaryHeap<Reverse<Box<FactorStorage>>>, mut cur_idx: usize) -> io::Result<usize> {
    while let Some(Reverse(storage)) = heap.peek() {
        if cur_idx == storage.0 {
            writeln!(stdout, "{}:{}", storage.1, storage.2)?;
            cur_idx += 1;
            heap.pop();
        } else {
            //heap.push(Reverse(storage));
            break;
        }
    }

    Ok(cur_idx)
}

pub fn uumain(args: impl uucore::Args) -> i32 {
    let matches = app!(SYNTAX, SUMMARY, LONG_HELP).parse(args.collect_str());
    //let stdout = stdout();
    //let mut w = io::BufWriter::new(stdout.lock());

    let (send, recv) = mpsc::channel();//mpsc::sync_channel(10000);//mpsc::sync_channel(rayon::current_num_threads());

    let print_thread = thread::spawn(|| {
        const PROCESS_SIZE: usize = 1000;

        let mut cur_idx = 0;

        let stdout = stdout();
        let mut w = io::BufWriter::new(stdout.lock());

        let mut heap = BinaryHeap::new();
        for elem in recv.into_iter() {
            heap.push(Reverse(elem));
            if heap.len() >= PROCESS_SIZE {
                cur_idx = process_elems(&mut w, &mut heap, cur_idx).unwrap();
            }
        }
        process_elems(&mut w, &mut heap, cur_idx).unwrap();

        assert!(heap.len() == 0);
    });

    if matches.free.is_empty() {
        let stdin = stdin();

        // XXX: collect() is wrong
        //for line in stdin.lock().lines() {
        let lines: Vec<String> = stdin.lock().lines().flat_map(|line| {
            let line = line.unwrap();
            let v: Vec<String> = line.split_whitespace().map(|s| s.to_owned()).collect();
            v.into_iter()
        }).collect();

        lines
            .par_iter()
            .enumerate()
            //.for_each(|(idx, line)| {
            //    line.as_ref().unwrap()
            //        .split_whitespace()
                    //.enumerate()
                    
                //line
            //        .par_bridge()
                    .try_for_each_with(send.clone(), |s, (idx, number)| {//(_idx, number)| {
                        print_factors_str(number, idx, s)
                    });
            //});

        drop(send);
        /*for line in stdin.lock().lines() {
            for number in line.unwrap().split_whitespace() {
                if let Err(e) = print_factors_str(number, &mut w) {
                    show_warning!("{}: {}", number, e);
                }
            }
        }*/
    } else {
        let res = matches.free.par_iter()
            .enumerate()
            .try_for_each_with(send, |s, (idx, number)| {
                print_factors_str(number, idx, s)
            });
       /* if let Err(e) = res {
            show_warning!("{}: {}", 
        for number in &matches.free.par_iter() {
            if let Err(e) = print_factors_str(number, &mut w) {
                show_warning!("{}: {}", number, e);
            }
        }*/
    }

    if let Err(e) = print_thread.join() {
        // TODO
        //show_error!("{}", e);
    }

    if let Err(e) = stdout().flush() {
        show_error!("{}", e);
    }

    0
}

#[cfg(test)]
mod tests {
    use super::factor;

    #[test]
    fn factor_recombines_small() {
        assert!((1..10_000)
            .map(|i| 2 * i + 1)
            .all(|i| factor(i).product() == i));
    }

    #[test]
    fn factor_recombines_overflowing() {
        assert!((0..250)
            .map(|i| 2 * i + 2u64.pow(32) + 1)
            .all(|i| factor(i).product() == i));
    }

    #[test]
    fn factor_recombines_strong_pseudoprime() {
        // This is a strong pseudoprime (wrt. miller_rabin::BASIS)
        //  and triggered a bug in rho::factor's codepath handling
        //  miller_rabbin::Result::Composite
        let pseudoprime = 17179869183;
        for _ in 0..20 {
            // Repeat the test 20 times, as it only fails some fraction
            // of the time.
            assert!(factor(pseudoprime).product() == pseudoprime);
        }
    }
}
