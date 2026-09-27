//! Go `net/netip` subset (go1.26.8 `src/net/netip/netip.go`,
//! `src/net/netip/uint128.go`; identical in go1.26.4): `ParseAddr` and
//! `Addr.Is4`, which `net/url` `parseHost` calls, and what they call. Other
//! `net/netip` functions are not ported.
//!
//! PORT: Go reads the bytes of a string. The port reads the Go bytes of the
//! port form (`scanner_util::go_string_bytes`), so indexes and slices are Go
//! byte offsets. A Go string made from a slice of those bytes is in the
//! value form (`scanner_util::go_value_from_bytes`).

use crate::prelude::*;

use crate::gostd::errors::{self, GoError};
use crate::gostd::strconv;
use std::fmt;

// Go: net/netip/uint128.go:13 uint128
/// uint128 represents a uint128 using two uint64s.
///
/// When the methods below mention a bit number, bit 0 is the most
/// significant bit (in hi) and bit 127 is the lowest (lo&1).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Uint128 {
    hi: u64,
    lo: u64,
}

// Go: net/netip/netip.go:37 Addr
/// Addr represents an IPv4 or IPv6 address (with or without a scoped
/// addressing zone), similar to [net.IP] or [net.IPAddr].
///
/// Unlike [net.IP] or [net.IPAddr], Addr is a comparable value
/// type (it supports == and can be a map key) and is immutable.
///
/// The zero Addr is not a valid IP address.
/// Addr{} is distinct from both 0.0.0.0 and ::.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Addr {
    /// addr is the hi and lo bits of an IPv6 address. If z==z4,
    /// hi and lo contain the IPv4-mapped IPv6 address.
    ///
    /// hi and lo are constructed by interpreting a 16-byte IPv6
    /// address as a big-endian 128-bit number. The most significant
    /// bits of that number go into hi, the rest into lo.
    addr: Uint128,

    /// Details about the address, wrapped up together and canonicalized.
    ///
    /// PORT: Go `unique.Handle[addrDetail]`. Two handles are equal when
    /// their values are equal, so the port keeps the value. `None` is the
    /// zero handle (`z0`).
    z: Option<AddrDetail>,
}

// Go: net/netip/netip.go:60 addrDetail
/// addrDetail represents the details of an Addr, like address family and IPv6 zone.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AddrDetail {
    is_v6: bool,     // IPv4 is false, IPv6 is true.
    zone_v6: String, // != "" only if IsV6 is true.
}

// Go: net/netip/netip.go:67 z0, z4, z6noz
// z0, z4, and z6noz are sentinel Addr.z values.
// See the Addr type's field docs.
const Z0: Option<AddrDetail> = None;
const Z4: Option<AddrDetail> = Some(AddrDetail {
    is_v6: false,
    zone_v6: String::new(),
});
const Z6NOZ: Option<AddrDetail> = Some(AddrDetail {
    is_v6: true,
    zone_v6: String::new(),
});

// Go: net/netip/netip.go:85 IPv6Unspecified
/// IPv6Unspecified returns the IPv6 unspecified address "::".
pub fn ipv6_unspecified() -> Addr {
    Addr {
        addr: Uint128::default(),
        z: Z6NOZ,
    }
}

// Go: net/netip/netip.go:91 AddrFrom4
/// AddrFrom4 returns the address of the IPv4 address given by the bytes in addr.
pub fn addr_from4(addr: [u8; 4]) -> Addr {
    Addr {
        addr: Uint128 {
            hi: 0,
            lo: 0xffff00000000
                | u64::from(addr[0]) << 24
                | u64::from(addr[1]) << 16
                | u64::from(addr[2]) << 8
                | u64::from(addr[3]),
        },
        z: Z4,
    }
}

// Go: net/netip/netip.go:101 AddrFrom16
/// AddrFrom16 returns the IPv6 address given by the bytes in addr.
/// An IPv4-mapped IPv6 address is left as an IPv6 address.
/// (Use Unmap to convert them if needed.)
pub fn addr_from16(addr: [u8; 16]) -> Addr {
    Addr {
        addr: Uint128 {
            // Go: byteorder.BEUint64
            hi: u64::from_be_bytes(addr[..8].try_into().expect("8 bytes")),
            lo: u64::from_be_bytes(addr[8..].try_into().expect("8 bytes")),
        },
        z: Z6NOZ,
    }
}

// Go: net/netip/netip.go:114 ParseAddr
/// ParseAddr parses s as an IP address, returning the result. The string
/// s can be in dotted decimal ("192.0.2.1"), IPv6 ("2001:db8::68"),
/// or IPv6 with a scoped addressing zone ("fe80::1cc0:3e8c:119f:c2e1%ens18").
pub fn parse_addr(s: &str) -> Result<Addr, GoError> {
    let b = go_string_bytes(s);
    for i in 0..b.len() {
        match b[i] {
            b'.' => return parse_ipv4(s),
            b':' => return parse_ipv6(s),
            b'%' => {
                // Assume that this was trying to be an IPv6 address with
                // a zone specifier, but the address is missing.
                return Err(ParseAddrError::err(s, "missing IPv6 address", b""));
            }
            _ => {}
        }
    }
    Err(ParseAddrError::err(s, "unable to parse IP", b""))
}

// Go: net/netip/netip.go:140 parseAddrError
#[derive(Clone, Debug, PartialEq, Eq)]
struct ParseAddrError {
    in_: String,       // the string given to ParseAddr
    msg: &'static str, // an explanation of the parse failure
    at: String,        // optionally, the unparsed portion of in at which the error occurred.
}

impl ParseAddrError {
    /// Go `parseAddrError{in: in, msg: msg, at: at}` as an `error`. `at`
    /// holds Go bytes; empty means no `at`.
    fn err(in_: &str, msg: &'static str, at: &[u8]) -> GoError {
        errors::from_value(ParseAddrError {
            in_: in_.to_string(),
            msg,
            at: go_value_from_bytes(at).into_owned(),
        })
    }
}

impl fmt::Display for ParseAddrError {
    // Go: net/netip/netip.go:146 Error
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q = strconv::quote;
        if !self.at.is_empty() {
            return write!(
                f,
                "ParseAddr({}): {} (at {})",
                q(&self.in_),
                self.msg,
                q(&self.at)
            );
        }
        write!(f, "ParseAddr({}): {}", q(&self.in_), self.msg)
    }
}

// Go: net/netip/netip.go:154 parseIPv4Fields
/// PORT: `off` and `end` are offsets in the Go bytes of `in_`.
fn parse_ipv4_fields(in_: &str, off: usize, end: usize, fields: &mut [u8]) -> Result<(), GoError> {
    let (mut val, mut pos) = (0i32, 0usize);
    let mut dig_len = 0; // number of digits in current octet
    let in_bytes = go_string_bytes(in_);
    let s = &in_bytes[off..end];
    for i in 0..s.len() {
        if s[i].is_ascii_digit() {
            if dig_len == 1 && val == 0 {
                return Err(ParseAddrError::err(
                    in_,
                    "IPv4 field has octet with leading zero",
                    b"",
                ));
            }
            val = val * 10 + i32::from(s[i]) - i32::from(b'0');
            dig_len += 1;
            if val > 255 {
                return Err(ParseAddrError::err(in_, "IPv4 field has value >255", b""));
            }
        } else if s[i] == b'.' {
            // .1.2.3
            // 1.2.3.
            // 1..2.3
            if i == 0 || i == s.len() - 1 || s[i - 1] == b'.' {
                return Err(ParseAddrError::err(
                    in_,
                    "IPv4 field must have at least one digit",
                    &s[i..],
                ));
            }
            // 1.2.3.4.5
            if pos == 3 {
                return Err(ParseAddrError::err(in_, "IPv4 address too long", b""));
            }
            fields[pos] = val as u8;
            pos += 1;
            val = 0;
            dig_len = 0;
        } else {
            return Err(ParseAddrError::err(in_, "unexpected character", &s[i..]));
        }
    }
    if pos < 3 {
        return Err(ParseAddrError::err(in_, "IPv4 address too short", b""));
    }
    fields[3] = val as u8;
    Ok(())
}

// Go: net/netip/netip.go:195 parseIPv4
/// parseIPv4 parses s as an IPv4 address (in form "192.168.0.1").
fn parse_ipv4(s: &str) -> Result<Addr, GoError> {
    let mut fields = [0u8; 4];
    parse_ipv4_fields(s, 0, go_len(s), &mut fields)?;
    Ok(addr_from4(fields))
}

// Go: net/netip/netip.go:205 parseIPv6
/// parseIPv6 parses s as an IPv6 address (in form "2001:db8::68").
fn parse_ipv6(in_: &str) -> Result<Addr, GoError> {
    let in_bytes = go_string_bytes(in_);
    let mut s: &[u8] = &in_bytes;

    // Split off the zone right from the start. Yes it's a second scan
    // of the string, but trying to handle it inline makes a bunch of
    // other inner loop conditionals more expensive, and it ends up
    // being slower.
    let mut zone: &[u8] = b"";
    // Go: bytealg.IndexByteString
    if let Some(i) = memchr::memchr(b'%', s) {
        (s, zone) = (&s[..i], &s[i + 1..]);
        if zone.is_empty() {
            // Not allowed to have an empty zone if explicitly specified.
            return Err(ParseAddrError::err(
                in_,
                "zone must be a non-empty string",
                b"",
            ));
        }
    }

    let mut ip = [0u8; 16];
    let mut ellipsis: isize = -1; // position of ellipsis in ip

    // Might have leading ellipsis
    if s.len() >= 2 && s[0] == b':' && s[1] == b':' {
        ellipsis = 0;
        s = &s[2..];
        // Might be only ellipsis
        if s.is_empty() {
            return Ok(ipv6_unspecified().with_zone(&go_value_from_bytes(zone)));
        }
    }

    // Loop, parsing hex numbers followed by colon.
    let mut i = 0usize;
    while i < 16 {
        // Hex number. Similar to parseIPv4, inlining the hex number
        // parsing yields a significant performance increase.
        let mut off = 0usize;
        let mut acc = 0u32;
        while off < s.len() {
            let c = s[off];
            if c.is_ascii_digit() {
                acc = (acc << 4) + u32::from(c - b'0');
            } else if (b'a'..=b'f').contains(&c) {
                acc = (acc << 4) + u32::from(c - b'a' + 10);
            } else if (b'A'..=b'F').contains(&c) {
                acc = (acc << 4) + u32::from(c - b'A' + 10);
            } else {
                break;
            }
            if off > 3 {
                //more than 4 digits in group, fail.
                return Err(ParseAddrError::err(
                    in_,
                    "each group must have 4 or less digits",
                    s,
                ));
            }
            if acc > u32::from(u16::MAX) {
                // Overflow, fail.
                return Err(ParseAddrError::err(in_, "IPv6 field has value >=2^16", s));
            }
            off += 1;
        }
        if off == 0 {
            // No digits found, fail.
            return Err(ParseAddrError::err(
                in_,
                "each colon-separated field must have at least one digit",
                s,
            ));
        }

        // If followed by dot, might be in trailing IPv4.
        if off < s.len() && s[off] == b'.' {
            if ellipsis < 0 && i != 12 {
                // Not the right place.
                return Err(ParseAddrError::err(
                    in_,
                    "embedded IPv4 address must replace the final 2 fields of the address",
                    s,
                ));
            }
            if i + 4 > 16 {
                // Not enough room.
                return Err(ParseAddrError::err(
                    in_,
                    "too many hex fields to fit an embedded IPv4 at the end of the address",
                    s,
                ));
            }

            let mut end = in_bytes.len();
            if !zone.is_empty() {
                end -= zone.len() + 1;
            }
            parse_ipv4_fields(in_, end - s.len(), end, &mut ip[i..i + 4])?;
            s = b"";
            i += 4;
            break;
        }

        // Save this 16-bit chunk.
        ip[i] = (acc >> 8) as u8;
        ip[i + 1] = acc as u8;
        i += 2;

        // Stop at end of string.
        s = &s[off..];
        if s.is_empty() {
            break;
        }

        // Otherwise must be followed by colon and more.
        if s[0] != b':' {
            return Err(ParseAddrError::err(
                in_,
                "unexpected character, want colon",
                s,
            ));
        } else if s.len() == 1 {
            return Err(ParseAddrError::err(
                in_,
                "colon must be followed by more characters",
                s,
            ));
        }
        s = &s[1..];

        // Look for ellipsis.
        if s[0] == b':' {
            if ellipsis >= 0 {
                // already have one
                return Err(ParseAddrError::err(in_, "multiple :: in address", s));
            }
            ellipsis = i as isize;
            s = &s[1..];
            if s.is_empty() {
                // can be at end
                break;
            }
        }
    }

    // Must have used entire string.
    if !s.is_empty() {
        return Err(ParseAddrError::err(
            in_,
            "trailing garbage after address",
            s,
        ));
    }

    // If didn't parse enough, expand ellipsis.
    if i < 16 {
        if ellipsis < 0 {
            return Err(ParseAddrError::err(in_, "address string too short", b""));
        }
        let n = 16 - i;
        let mut j = i as isize - 1;
        while j >= ellipsis {
            ip[j as usize + n] = ip[j as usize];
            j -= 1;
        }
        let e = ellipsis as usize;
        ip[e..e + n].fill(0);
    } else if ellipsis >= 0 {
        // Ellipsis must represent at least one 0 group.
        return Err(ParseAddrError::err(
            in_,
            "the :: must expand to at least one field of zeros",
            b"",
        ));
    }
    Ok(addr_from16(ip).with_zone(&go_value_from_bytes(zone)))
}

impl Addr {
    // Go: net/netip/netip.go:460 Is4
    /// Is4 reports whether ip is an IPv4 address.
    ///
    /// It returns false for IPv4-mapped IPv6 addresses. See [Addr.Unmap].
    pub fn is4(&self) -> bool {
        self.z == Z4
    }

    // Go: net/netip/netip.go:473 Is6
    /// Is6 reports whether ip is an IPv6 address, including IPv4-mapped
    /// IPv6 addresses.
    pub fn is6(&self) -> bool {
        self.z != Z0 && self.z != Z4
    }

    // Go: net/netip/netip.go:491 WithZone
    /// WithZone returns an IP that's the same as ip but with the provided
    /// zone. If zone is empty, the zone is removed. If ip is an IPv4
    /// address, WithZone is a no-op and returns ip unchanged.
    pub fn with_zone(mut self, zone: &str) -> Addr {
        if !self.is6() {
            return self;
        }
        if zone.is_empty() {
            self.z = Z6NOZ;
            return self;
        }
        self.z = Some(AddrDetail {
            is_v6: true,
            zone_v6: zone.to_string(),
        });
        self
    }
}
