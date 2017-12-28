#![crate_name = "uu_dd"]
#![recursion_limit = "128"]

/*
 * This file is part of the uutils coreutils package.
 *
 * (c) Alex Lyon <arcterus@mail.com>
 *
 * For the full copyright and license information, please view the LICENSE file
 * that was distributed with this source code.
 */

#[macro_use] extern crate uucore;
#[macro_use] extern crate quick_error;
extern crate number_prefix;
extern crate term;

use number_prefix::{PrefixNames, Standalone, Prefixed};
use term::Terminal;
use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt;
use std::convert::From;
use std::num::ParseIntError;
use std::str::FromStr;
use std::fs::File;
use std::time::{Duration, Instant};
use std::io::{self, Read, Write, ErrorKind};

type Result<T> = std::result::Result<T, Error>;

struct Options<'a> {
    input_file: Option<&'a OsStr>,
    output_file: Option<&'a OsStr>,
    ibs: u64,   // input bytes per block (default is 512)
    obs: u64,   // output bytes per block (default is 512)
    cbs: Option<u64>,
    skip: Option<u64>,
    seek: Option<u64>,
    count: Option<u64>,
    status: Status,
    conv: Vec<Conversion>,
    iflag: Vec<Flag>,
    oflag: Vec<Flag>
}

impl<'a> Default for Options<'a> {
    fn default() -> Options<'a> {
        Options {
            input_file: None,
            output_file: None,
            ibs: 512,
            obs: 512,
            cbs: None,
            skip: None,
            seek: None,
            count: None,
            status: Status::Default,
            conv: vec![],
            iflag: vec![],
            oflag: vec![],
        }
    }
}

#[derive(PartialEq)]
enum Status {
    Default,
    None,
    NoTransfer,
    Progress
}

#[derive(Clone, Copy, PartialEq)]
enum Conversion {
    ASCII,
    EBCDIC,
    IBM,
    Block,
    Unblock,
    Lowercase,
    Uppercase,
    Sparse,
    Swab,
    Sync,

    // the following are actually file flags
    Excl,
    NoCreate,
    NoTruncate,
    NoError,
    FileDataSync,
    FileSync
}

/// File flags for use with the iflag and oflag options
enum Flag {
    Append,
    Concurrent,
    Direct,
    Directory,
    DataSync,
    Sync,
    NoCache,
    Nonblock,
    NoATime,
    NoCTTY,
    NoFollow,
    NoLinks,
    Binary,
    Text,
    FullBlock,
    CountBytes,
    SkipBytes,
    SeekBytes
}

fn parse_arguments<T: AsRef<OsStr>>(args: &[T]) -> Result<Options> {
    let mut options = Options::default();

    for arg in args {
        let (option, param) = split_string(arg.as_ref())?;
        match option.to_str() {
            Some("if") => {
                options.input_file = Some(param);
            },
            Some("of") => {
                options.output_file = Some(param);
            },
            Some("ibs") => {
                // TODO: this (and the others) should accept stuff like 1M and 4k
                options.ibs = convert(param)?;
            },
            Some("obs") => {
                options.obs = convert(param)?;
            },
            Some("bs") => {
                let size = convert(param)?;
                options.ibs = size;
                options.obs = size;
            }
            Some("cbs") => {
                options.cbs = Some(convert(param)?);
            }
            Some("skip") => {
                options.skip = Some(convert(param)?);
            }
            Some("seek") => {
                options.seek = Some(convert(param)?);
            }
            Some("count") => {
                options.count = Some(convert(param)?);
            }
            Some("status") => {
                options.status = match param.to_str() {
                    Some("none") => Status::None,
                    Some("noxfer") => Status::NoTransfer,
                    Some("progress") => Status::Progress,
                    _ => {
                        let msg = format!("expected one of 'none', 'noxfer', 'progress' for status option but found '{}'", param.to_string_lossy());
                        return Err(Error::InvalidArgument(msg));
                    }
                };
            }
            Some("conv") => {
                parse_conv(&mut options.conv, param)?;
            }
            _ => {
                return Err(Error::InvalidArgument(format!("{}", option.to_string_lossy())));
            }
        }
    }

    validate_options(options)
}

#[cfg(unix)]
fn split_string(arg: &OsStr) -> Result<(&OsStr, &OsStr)> {
    let mut iter = arg.as_bytes().splitn(2, |&byte| byte == b'=');

    let first = next_or_err(&mut iter)?;
    let second = next_or_err(&mut iter)?;

    Ok((OsStr::from_bytes(first), OsStr::from_bytes(second)))
}

fn next_or_err<T: Iterator>(iter: &mut T) -> Result<T::Item> {
    iter.next().ok_or_else(|| {
        Error::InvalidArgument("argument missing '='".to_string())
    })
}

#[cfg(windows)]
fn split_string(arg: &OsStr) -> Result<(&OsStr, &OsStr)> {
    compile_error!("OsStr splitting for argument parsing does not yet work for Windows");
}

fn convert<T: FromStr>(arg: &OsStr) -> Result<T>
    where Error: From<T::Err>
{
    Ok(T::from_str(arg.to_str().ok_or_else(|| {
        Error::InvalidArgument(format!("could not convert '{}' to a {}",
                                       arg.to_string_lossy(),
                                       stringify!(T)))
    })?)?)
}

fn parse_conv(conv: &mut Vec<Conversion>, param: &OsStr) -> Result<()> {
    let param_str = param.to_str().ok_or_else(|| {
        Error::InvalidArgument("could not parse arguments for conv".to_string())
    })?;

    // whether an encoding was specified as they are mutually exclusive
    let mut encoding = None;
    let mut block = None;
    let mut case = None;
    let mut create = None;

    for option in param_str.split(',') {
        match option {
            "ascii" => {
                check_encoding(conv, &mut encoding, Conversion::ASCII)?;
                check_block(conv, &mut block, Conversion::Unblock)?;
            }
            "ebcdic" => {
                check_encoding(conv, &mut encoding, Conversion::EBCDIC)?;
                check_block(conv, &mut block, Conversion::Block)?;
            }
            "ibm" => {
                check_encoding(conv, &mut encoding, Conversion::IBM)?;
                check_block(conv, &mut block, Conversion::Block)?;
            }
            "block" => check_block(conv, &mut block, Conversion::Block)?,
            "unblock" => check_block(conv, &mut block, Conversion::Unblock)?,
            "lcase" => check_case(conv, &mut case, Conversion::Lowercase)?,
            "ucase" => check_case(conv, &mut case, Conversion::Uppercase)?,
            "sparse" => conv.push(Conversion::Sparse),
            "swab" => conv.push(Conversion::Swab),
            "sync" => conv.push(Conversion::Sync),

            // file flags basically
            "excl" => check_create(conv, &mut create, Conversion::Excl)?,
            "nocreat" => check_create(conv, &mut create, Conversion::NoCreate)?,
            "notrunc" => conv.push(Conversion::NoTruncate),
            "noerror" => conv.push(Conversion::NoError),
            "fdatasync" => conv.push(Conversion::FileDataSync),
            "fsync" => conv.push(Conversion::FileSync),
            _ => {
                return Err(Error::InvalidArgument(format!("invalid argument for conv: '{}'", param_str)));
            }
        }
    }

    Ok(())
}

fn check_encoding(conv: &mut Vec<Conversion>, encoding: &mut Option<Conversion>, option: Conversion) -> Result<()> {
    check_exclusive(conv, encoding, option, "'ascii', 'ebcdic', and 'ibm' are mutually exclusive")
}

fn check_block(conv: &mut Vec<Conversion>, block: &mut Option<Conversion>, option: Conversion) -> Result<()> {
    check_exclusive(conv, block, option, "'block' and 'unblock' are mutually exclusive")
}

fn check_case(conv: &mut Vec<Conversion>, case: &mut Option<Conversion>, option: Conversion) -> Result<()> {
    check_exclusive(conv, case, option, "'lcase' and 'ucase' are mutually exclusive")
}

fn check_create(conv: &mut Vec<Conversion>, create: &mut Option<Conversion>, option: Conversion) -> Result<()> {
    check_exclusive(conv, create, option, "'excl' and 'nocreat' are mutually exclusive")
}

fn check_exclusive(conv: &mut Vec<Conversion>, exclusive: &mut Option<Conversion>, option: Conversion, msg: &str) -> Result<()> {
    match *exclusive {
        None => {
            conv.push(option);
            *exclusive = Some(option);
        }
        Some(opt) if opt == option => {}
        Some(_) => {
            return Err(Error::InvalidArgument(msg.to_string()));
        }
    }

    Ok(())
}

fn validate_options(options: Options) -> Result<Options> {
    // TODO: actually validate (need to figure out which options need validation first)
    Ok(options)
}

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        /// Simple io::Error wrapper
        IoErr(err: io::Error) { from() cause(err) display("{}", err) }

        /// Wrapper for io::Error with path context
        IoErrContext(err: io::Error, path: String) {
            display("{}: {}", path, err)
            context(path: &'a str, err: io::Error) -> (err, path.to_owned())
            cause(err)
        }

        /// General error
        Error(err: String) {
            display("{}", err)
            from(err: String) -> (err)
            from(err: &'static str) -> (err.to_string())
        }

        /// Wrapper for ParseIntError
        ParseIntError(err: ParseIntError) { from() }

        /// Invalid command-line argument
        InvalidArgument(description: String) { display("{}", description) }

        /// Failure to initialize StderrTerminal
        StderrTerminal {}

        /// Wrapper for term::Error
        TermError(err: term::Error) { from() }

        /// All standard options are included as an an implementation
        /// path, but those that are not implemented yet should return
        /// a NotImplemented error.
        NotImplemented(opt: String) { display("Option '{}' not yet implemented.", opt) }
    }
}

pub fn uumain(args: Vec<String>) -> i32 {
    let options = crash_if_err!(1, parse_arguments(&args[1..]));

    // XXX: should we actually be using locked stdin/stdout?
    // TODO: handle iflag
    let stdin;
    let reader = if let Some(pathstr) = options.input_file {
        stdin = None;
        Box::new(crash_if_err!(1, File::open(pathstr))) as Box<Read>
    } else {
        stdin = Some(io::stdin());
        let reader = Box::new(stdin.as_ref().unwrap().lock());
        reader as Box<Read>
    };

    // TODO: handle oflag
    let stdout;
    let writer = if let Some(pathstr) = options.output_file {
        stdout = None;
        Box::new(crash_if_err!(1, File::create(pathstr))) as Box<Write>
    } else {
        stdout = Some(io::stdout());
        let writer = Box::new(stdout.as_ref().unwrap().lock());
        writer as Box<Write>
    };

    match exec(options, reader, writer) {
        Ok(()) => 0,
        Err(err) => {
            show_error!("{}", err);
            1
        }
    }
}

fn exec<R: Read, W: Write>(options: Options, mut reader: R, mut writer: W) -> Result<()> {
    #[derive(Default)]
    struct Block {
        full: u64,
        partial: u64
    }

    let mut buffer = vec![0; options.ibs as usize];

    let one_sec = Duration::from_secs(1);
    let now = Instant::now();
    let mut timer = now.clone();

    let mut written = 0;
    let mut inblocks = Block::default();
    let mut outblocks = Block::default();

    let mut stderr = term::stderr().ok_or_else(|| {
        Error::StderrTerminal
    })?;

    loop {
        match reader.read(&mut buffer) {
            Ok(size) if size == 0 => break,
            Ok(size) => {
                if (size as u64) < options.ibs {
                    // TODO: i think GNU dd warns if this occurs and suggests using iflag=fullblock
                    inblocks.partial += 1;
                } else {
                    inblocks.full += 1;
                }

                // write the buffer
                // TODO: make this actually heed obs
                writer.write_all(&buffer)?;

                // FIXME: when this heeds obs, all the "ibs" below should be changed to obs
                if (size as u64) < options.ibs {
                    outblocks.partial += 1;
                } else {
                    outblocks.full += 1;
                }

                written += options.ibs;
            }
            Err(ref err) if err.kind() == ErrorKind::BrokenPipe => {
                // FIXME: might need to set a flag if it's a broken pipe to avoid printing or
                // something later
                break;
            }
            Err(err) => return Err(err.into())
        }

        if options.status == Status::Progress {
            if timer.elapsed() >= one_sec {
                timer += one_sec;
                display_progress(&mut *stderr, now.elapsed(), written)?;
            }
        }
    }

    // TODO: check if pipe error?
    // TODO: need to check if ctrl-c so we can print status info when it occurs
    if options.status == Status::Progress {
        writeln!(stderr)?;
    }
    if options.status != Status::None {
        writeln!(stderr, "{}+{} records in", inblocks.full, inblocks.partial)?;
        writeln!(stderr, "{}+{} records out", outblocks.full, outblocks.partial)?;

        if options.status != Status::NoTransfer {
            display_progress(&mut *stderr, now.elapsed(), written)?;
            writeln!(stderr)?;
        }
    }

    Ok(())
}

fn display_progress<T: Write>(output: &mut Terminal<Output = T>, duration: Duration, written: u64) -> Result<()> {
    output.carriage_return()?;
    output.delete_line()?;

    let (decimal, dec_prefix) = match number_prefix::decimal_prefix(written as f64) {
        Standalone(bytes) => (bytes, ""),
        Prefixed(prefix, bytes) => (bytes, prefix.symbol())
    };

    let (binary, bin_prefix) = match number_prefix::binary_prefix(written as f64) {
        Standalone(bytes) => (bytes, ""),
        Prefixed(prefix, bytes) => (bytes, prefix.symbol())
    };

    let (transfer, transfer_prefix) = match number_prefix::decimal_prefix(written as f64 / duration.as_secs() as f64) {
        Standalone(bytes) => (bytes, ""),
        Prefixed(prefix, bytes) => (bytes, prefix.symbol())
    };

    // FIXME: this needs to be formatted for more than just seconds
    let time = duration.as_secs() as f64 + duration.subsec_nanos() as f64 * 1e-9;

    write!(output, "{} bytes ({:.0} {}B, {:.0} {}B) copied, {:.5} s, {:.1} {}B/s", written, decimal, dec_prefix, binary, bin_prefix, time, transfer, transfer_prefix)?;

    Ok(())
}
