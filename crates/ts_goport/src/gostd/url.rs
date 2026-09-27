//! Go `net/url` subset (go1.26.8 `src/net/url/url.go`,
//! `src/net/url/encoding_table.go`; identical in go1.26.4): `Parse` for
//! `lsproto.DocumentUri.FileName`, `PathEscape`, `QueryEscape`,
//! `PathUnescape` and what they call. Other `net/url` functions are not
//! ported.
//!
//! PORT: Go strings hold any bytes. A port string is the port form of a Go
//! string (see `scanner_util::GO_STRING_MARKER`). `unescape` and `escape`
//! read its Go bytes (`go_string_bytes`). A string that `unescape` builds
//! from bytes, for example "caf\xff" from "caf%FF", is in the value form
//! (`go_value_from_bytes`), like a file name from the OS. `escape` escapes
//! every byte that is not ASCII, so its result is ASCII.

use crate::prelude::*;

use crate::gostd::errors::{self, GoError};
use crate::gostd::netip;
use crate::gostd::strconv;
use std::fmt;

// Go: net/url/url.go:30 urlstrictcolons
// PORT: GODEBUG is not read. The go1.26 default (strict colons for http and
// https, Old "0" not set) applies.
fn urlstrictcolons_value() -> &'static str {
    ""
}

// Go: net/url/url.go:33 Error
/// Error reports an error and the operation and URL that caused it.
#[derive(Clone, Debug, PartialEq)]
pub struct Error {
    pub op: String,
    pub url: String,
    pub err: GoError,
}

impl Error {
    // Go: net/url/url.go:39 Unwrap
    pub fn unwrap(&self) -> GoError {
        self.err.clone()
    }

    // Go: net/url/url.go:40 Error
    pub fn error(&self) -> String {
        format!(
            "{} {}: {}",
            self.op,
            strconv::quote(&self.url),
            self.err.error()
        )
    }

    /// Go `&Error{...}` as an `error` value.
    /// PORT: Go compares `*Error` values by pointer; the port compares the
    /// fields. No caller compares them.
    fn into_go_error(self) -> GoError {
        let inner = self.err.clone();
        errors::from_value_with_unwrap(self, inner)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.error())
    }
}

const UPPERHEX: &[u8; 16] = b"0123456789ABCDEF";

// Go: net/url/url.go:58 ishex
fn ishex(c: u8) -> bool {
    TABLE[c as usize] & HEX_CHAR != 0
}

// Go: net/url/url.go:63 unhex
/// Precondition: ishex(c) is true.
fn unhex(c: u8) -> u8 {
    9 * (c >> 6) + (c & 15)
}

// Go: net/url/url.go:67 EscapeError
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EscapeError(pub String);

impl fmt::Display for EscapeError {
    // Go: net/url/url.go:69 Error
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid URL escape {}", strconv::quote(&self.0))
    }
}

// Go: net/url/url.go:73 InvalidHostError
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidHostError(pub String);

impl fmt::Display for InvalidHostError {
    // Go: net/url/url.go:75 Error
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid character {} in host name",
            strconv::quote(&self.0)
        )
    }
}

// Go: net/url/url.go:80 shouldEscape
/// See the reference implementation in gen_encoding_table.go.
fn should_escape(c: u8, mode: Encoding) -> bool {
    TABLE[c as usize] & mode == 0
}

// Go: net/url/url.go:89 QueryUnescape
/// QueryUnescape does the inverse transformation of [QueryEscape],
/// converting each 3-byte encoded substring of the form "%AB" into the
/// hex-decoded byte 0xAB.
/// It returns an error if any % is not followed by two hexadecimal
/// digits.
pub fn query_unescape(s: &str) -> Result<String, GoError> {
    unescape(s, ENCODE_QUERY_COMPONENT)
}

// Go: net/url/url.go:100 PathUnescape
/// PathUnescape does the inverse transformation of [PathEscape],
/// converting each 3-byte encoded substring of the form "%AB" into the
/// hex-decoded byte 0xAB. It returns an error if any % is not followed
/// by two hexadecimal digits.
///
/// PathUnescape is identical to [QueryUnescape] except that it does not
/// unescape '+' to ' ' (space).
pub fn path_unescape(s: &str) -> Result<String, GoError> {
    unescape(s, ENCODE_PATH_SEGMENT)
}

// Go: net/url/url.go:106 unescape
/// unescape unescapes a string; the mode specifies
/// which section of the URL string is being unescaped.
fn unescape(s: &str, mode: Encoding) -> Result<String, GoError> {
    let b = go_string_bytes(s);
    let b: &[u8] = &b;
    // Count %, check that they're well-formed.
    let mut n = 0;
    let mut has_plus = false;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'%' => {
                n += 1;
                if i + 2 >= b.len() || !ishex(b[i + 1]) || !ishex(b[i + 2]) {
                    let mut e = &b[i..];
                    if e.len() > 3 {
                        e = &e[..3];
                    }
                    return Err(errors::from_value(EscapeError(go_string(e))));
                }
                // Per https://tools.ietf.org/html/rfc3986#page-21
                // in the host component %-encoding can only be used
                // for non-ASCII bytes.
                // But https://tools.ietf.org/html/rfc6874#section-2
                // introduces %25 being allowed to escape a percent sign
                // in IPv6 scoped-address literals. Yay.
                if mode == ENCODE_HOST && unhex(b[i + 1]) < 8 && &b[i..i + 3] != b"%25" {
                    return Err(errors::from_value(EscapeError(go_string(&b[i..i + 3]))));
                }
                if mode == ENCODE_ZONE {
                    // RFC 6874 says basically "anything goes" for zone identifiers
                    // and that even non-ASCII can be redundantly escaped,
                    // but it seems prudent to restrict %-escaped bytes here to those
                    // that are valid host name bytes in their unescaped form.
                    // That is, you can use escaping in the zone identifier but not
                    // to introduce bytes you couldn't just write directly.
                    // But Windows puts spaces here! Yay.
                    let v = (unhex(b[i + 1]) << 4) | unhex(b[i + 2]);
                    if &b[i..i + 3] != b"%25" && v != b' ' && should_escape(v, ENCODE_HOST) {
                        return Err(errors::from_value(EscapeError(go_string(&b[i..i + 3]))));
                    }
                }
                i += 3;
            }
            b'+' => {
                has_plus = mode == ENCODE_QUERY_COMPONENT;
                i += 1;
            }
            _ => {
                if (mode == ENCODE_HOST || mode == ENCODE_ZONE)
                    && b[i] < 0x80
                    && should_escape(b[i], mode)
                {
                    return Err(errors::from_value(InvalidHostError(go_string(
                        &b[i..i + 1],
                    ))));
                }
                i += 1;
            }
        }
    }

    if n == 0 && !has_plus {
        return Ok(s.to_string());
    }

    let unescaped_plus_sign = match mode {
        ENCODE_QUERY_COMPONENT => b' ',
        _ => b'+',
    };
    let mut t: Vec<u8> = Vec::with_capacity(b.len() - 2 * n);
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'%' => {
                // In the loop above, we established that unhex's precondition is
                // fulfilled for both s[i+1] and s[i+2].
                t.push((unhex(b[i + 1]) << 4) | unhex(b[i + 2]));
                i += 2;
            }
            b'+' => t.push(unescaped_plus_sign),
            _ => t.push(b[i]),
        }
        i += 1;
    }
    Ok(go_string(&t))
}

/// Go `string(b)` for Go bytes `b`, in the value form (see the module
/// comment). The bytes can hold invalid UTF-8, for example "%\xe6\x97" from
/// a slice that cuts a character.
fn go_string(b: &[u8]) -> String {
    go_value_from_bytes(b).into_owned()
}

// Go: net/url/url.go:186 QueryEscape
/// QueryEscape escapes the string so it can be safely placed
/// inside a [URL] query.
pub fn query_escape(s: &str) -> String {
    escape(s, ENCODE_QUERY_COMPONENT)
}

// Go: net/url/url.go:192 PathEscape
/// PathEscape escapes the string so it can be safely placed inside a [URL] path segment,
/// replacing special characters (including /) with %XX sequences as needed.
pub fn path_escape(s: &str) -> String {
    escape(s, ENCODE_PATH_SEGMENT)
}

// Go: net/url/url.go:196 escape
fn escape(s: &str, mode: Encoding) -> String {
    let b = go_string_bytes(s);
    let b: &[u8] = &b;
    let (mut space_count, mut hex_count) = (0, 0);
    for &c in b {
        if should_escape(c, mode) {
            if c == b' ' && mode == ENCODE_QUERY_COMPONENT {
                space_count += 1;
            } else {
                hex_count += 1;
            }
        }
    }

    if space_count == 0 && hex_count == 0 {
        return s.to_string();
    }

    let required = b.len() + 2 * hex_count;
    let mut t: Vec<u8> = vec![0; required];

    if hex_count == 0 {
        t.copy_from_slice(b);
        for i in 0..b.len() {
            if b[i] == b' ' {
                t[i] = b'+';
            }
        }
        return String::from_utf8(t).expect("escape writes ASCII");
    }

    let mut j = 0;
    for &c in b {
        if c == b' ' && mode == ENCODE_QUERY_COMPONENT {
            t[j] = b'+';
            j += 1;
        } else if should_escape(c, mode) {
            t[j] = b'%';
            t[j + 1] = UPPERHEX[(c >> 4) as usize];
            t[j + 2] = UPPERHEX[(c & 15) as usize];
            j += 3;
        } else {
            t[j] = c;
            j += 1;
        }
    }
    String::from_utf8(t).expect("escape writes ASCII")
}

// Go: net/url/url.go:276 URL
/// A URL represents a parsed URL (technically, a URI reference).
///
/// The general form represented is:
///
/// `[scheme:][//[userinfo@]host][/]path[?query][#fragment]`
///
/// URLs that do not start with a slash after the scheme are interpreted as:
///
/// `scheme:opaque[?query][#fragment]`
///
/// Note that the Path field is stored in decoded form: /%47%6f%2f becomes /Go/.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct URL {
    pub scheme: String,
    pub opaque: String,         // encoded opaque data
    pub user: Option<Userinfo>, // username and password information
    pub host: String,           // "host" or "host:port" (see Hostname and Port methods)
    pub path: String,           // path (relative paths may omit leading slash)
    pub fragment: String,       // fragment for references (without '#')

    /// RawQuery contains the encoded query values, without the initial '?'.
    /// Use URL.Query to decode the query.
    pub raw_query: String,

    /// RawPath is an optional field containing an encoded path hint.
    /// See the EscapedPath method for more details.
    ///
    /// In general, code should call EscapedPath instead of reading RawPath.
    pub raw_path: String,

    /// RawFragment is an optional field containing an encoded fragment hint.
    /// See the EscapedFragment method for more details.
    ///
    /// In general, code should call EscapedFragment instead of reading RawFragment.
    pub raw_fragment: String,

    /// ForceQuery indicates whether the original URL contained a query ('?') character.
    /// When set, the String method will include a trailing '?', even when RawQuery is empty.
    pub force_query: bool,

    /// OmitHost indicates the URL has an empty host (authority).
    /// When set, the String method will not include the host when it is empty.
    pub omit_host: bool,
}

// Go: net/url/url.go:311 User
/// User returns a [Userinfo] containing the provided username
/// and no password set.
pub fn user(username: &str) -> Userinfo {
    Userinfo {
        username: username.to_string(),
        password: String::new(),
        password_set: false,
    }
}

// Go: net/url/url.go:323 UserPassword
/// UserPassword returns a [Userinfo] containing the provided username
/// and password.
pub fn user_password(username: &str, password: &str) -> Userinfo {
    Userinfo {
        username: username.to_string(),
        password: password.to_string(),
        password_set: true,
    }
}

// Go: net/url/url.go:331 Userinfo
/// The Userinfo type is an immutable encapsulation of username and
/// password details for a [URL]. An existing Userinfo value is guaranteed
/// to have a username set (potentially empty, as allowed by RFC 2396),
/// and optionally a password.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Userinfo {
    username: String,
    password: String,
    password_set: bool,
}

impl Userinfo {
    // Go: net/url/url.go:338 Username
    /// Username returns the username.
    pub fn username(&self) -> String {
        self.username.clone()
    }

    // Go: net/url/url.go:346 Password
    /// Password returns the password in case it is set, and whether it is set.
    pub fn password(&self) -> (String, bool) {
        (self.password.clone(), self.password_set)
    }

    // Go: net/url/url.go:355 String
    /// String returns the encoded userinfo information in the standard form
    /// of "username[:password]".
    pub fn string(&self) -> String {
        let mut s = escape(&self.username, ENCODE_USER_PASSWORD);
        if self.password_set {
            s += ":";
            s += &escape(&self.password, ENCODE_USER_PASSWORD);
        }
        s
    }
}

// Go: net/url/url.go:369 getScheme
/// Maybe rawURL is of the form scheme:path.
/// (Scheme must be [a-zA-Z][a-zA-Z0-9+.-]*)
/// If so, return scheme, path; else return "", rawURL.
fn get_scheme(raw_url: &str) -> Result<(String, String), GoError> {
    let b = raw_url.as_bytes();
    for i in 0..b.len() {
        let c = b[i];
        if c.is_ascii_lowercase() || c.is_ascii_uppercase() {
            // do nothing
        } else if c.is_ascii_digit() || c == b'+' || c == b'-' || c == b'.' {
            if i == 0 {
                return Ok((String::new(), raw_url.to_string()));
            }
        } else if c == b':' {
            if i == 0 {
                return Err(errors::new("missing protocol scheme"));
            }
            return Ok((raw_url[..i].to_string(), raw_url[i + 1..].to_string()));
        } else {
            // we have encountered an invalid character,
            // so there is no valid scheme
            return Ok((String::new(), raw_url.to_string()));
        }
    }
    Ok((String::new(), raw_url.to_string()))
}

// Go: net/url/url.go:399 Parse
/// Parse parses a raw url into a [URL] structure.
///
/// The url may be relative (a path, without a host) or absolute
/// (starting with a scheme). Trying to parse a hostname and path
/// without a scheme is invalid but may not necessarily return an
/// error, due to parsing ambiguities.
pub fn parse(raw_url: &str) -> Result<URL, GoError> {
    // Cut off #frag
    let (u, frag) = match raw_url.split_once('#') {
        Some((u, frag)) => (u, frag),
        None => (raw_url, ""),
    };
    let mut url = match parse_unexported(u, false) {
        Ok(url) => url,
        Err(err) => {
            return Err(Error {
                op: "parse".to_string(),
                url: u.to_string(),
                err,
            }
            .into_go_error());
        }
    };
    if frag.is_empty() {
        return Ok(url);
    }
    if let Err(err) = url.set_fragment(frag) {
        return Err(Error {
            op: "parse".to_string(),
            url: raw_url.to_string(),
            err,
        }
        .into_go_error());
    }
    Ok(url)
}

// Go: net/url/url.go:420 ParseRequestURI
/// ParseRequestURI parses a raw url into a [URL] structure. It assumes that
/// url was received in an HTTP request, so the url is interpreted
/// only as an absolute URI or an absolute path.
pub fn parse_request_uri(raw_url: &str) -> Result<URL, GoError> {
    match parse_unexported(raw_url, true) {
        Ok(url) => Ok(url),
        Err(err) => Err(Error {
            op: "parse".to_string(),
            url: raw_url.to_string(),
            err,
        }
        .into_go_error()),
    }
}

// Go: net/url/url.go:432 parse
/// parse parses a URL from a string in one of two contexts. If
/// viaRequest is true, the URL is assumed to have arrived via an HTTP request,
/// in which case only absolute URLs or path-absolute relative URLs are allowed.
/// If viaRequest is false, all forms of relative URLs are allowed.
///
/// PORT: named `parse_unexported` because Go `Parse` is `parse` (plan
/// contract C1).
fn parse_unexported(raw_url: &str, via_request: bool) -> Result<URL, GoError> {
    let mut rest: String;

    if string_contains_ctl_byte(raw_url) {
        return Err(errors::new("net/url: invalid control character in URL"));
    }

    if raw_url.is_empty() && via_request {
        return Err(errors::new("empty url"));
    }
    let mut url = URL::default();

    if raw_url == "*" {
        url.path = "*".to_string();
        return Ok(url);
    }

    // Split off possible leading "http:", "mailto:", etc.
    // Cannot contain escaped characters.
    let (scheme, r) = get_scheme(raw_url)?;
    url.scheme = scheme;
    rest = r;
    url.scheme = url.scheme.to_lowercase();

    if rest.ends_with('?') && rest.matches('?').count() == 1 {
        url.force_query = true;
        rest.truncate(rest.len() - 1);
    } else {
        let (r, q) = match rest.split_once('?') {
            Some((r, q)) => (r.to_string(), q.to_string()),
            None => (rest.clone(), String::new()),
        };
        rest = r;
        url.raw_query = q;
    }

    if !rest.starts_with('/') {
        if !url.scheme.is_empty() {
            // We consider rootless paths per RFC 3986 as opaque.
            url.opaque = rest;
            return Ok(url);
        }
        if via_request {
            return Err(errors::new("invalid URI for request"));
        }

        // Avoid confusion with malformed schemes, like cache_object:foo/bar.
        // See golang.org/issue/16822.
        //
        // RFC 3986, §3.3:
        // In addition, a URI reference (Section 4.1) may be a relative-path reference,
        // in which case the first path segment cannot contain a colon (":") character.
        let segment = match rest.split_once('/') {
            Some((segment, _)) => segment,
            None => rest.as_str(),
        };
        if segment.contains(':') {
            // First path segment has colon. Not allowed in relative URL.
            return Err(errors::new(
                "first path segment in URL cannot contain colon",
            ));
        }
    }

    if (!url.scheme.is_empty() || !via_request && !rest.starts_with("///"))
        && rest.starts_with("//")
    {
        let mut authority = rest[2..].to_string();
        rest = String::new();
        if let Some(i) = authority.find('/') {
            rest = authority[i..].to_string();
            authority.truncate(i);
        }
        let (user, host) = parse_authority(&url.scheme, &authority)?;
        url.user = user;
        url.host = host;
    } else if !url.scheme.is_empty() && rest.starts_with('/') {
        // OmitHost is set to true when rawURL has an empty host (authority).
        // See golang.org/issue/46059.
        url.omit_host = true;
    }

    // Set Path and, optionally, RawPath.
    // RawPath is a hint of the encoding of Path. We don't want to set it if
    // the default escaping of Path is equivalent, to help make sure that people
    // don't rely on it in general.
    url.set_path(&rest)?;
    Ok(url)
}

// Go: net/url/url.go:512 parseAuthority
fn parse_authority(scheme: &str, authority: &str) -> Result<(Option<Userinfo>, String), GoError> {
    let i = authority.rfind('@');
    let host = match i {
        None => parse_host(scheme, authority)?,
        Some(i) => parse_host(scheme, &authority[i + 1..])?,
    };
    let Some(i) = i else {
        return Ok((None, host));
    };
    let userinfo = &authority[..i];
    if !valid_userinfo(userinfo) {
        return Err(errors::new("net/url: invalid userinfo"));
    }
    let user = if !userinfo.contains(':') {
        let userinfo = unescape(userinfo, ENCODE_USER_PASSWORD)?;
        self::user(&userinfo)
    } else {
        let (username, password) = userinfo.split_once(':').expect("contains ':'");
        let username = unescape(username, ENCODE_USER_PASSWORD)?;
        let password = unescape(password, ENCODE_USER_PASSWORD)?;
        user_password(&username, &password)
    };
    Ok((Some(user), host))
}

// Go: net/url/url.go:549 parseHost
/// parseHost parses host as an authority without user
/// information. That is, as host[:port].
fn parse_host(scheme: &str, host: &str) -> Result<String, GoError> {
    let open_bracket_idx = host.rfind('[');
    if open_bracket_idx.is_some_and(|i| i > 0) {
        return Err(errors::new("invalid IP-literal"));
    } else if open_bracket_idx == Some(0) {
        // Parse an IP-Literal in RFC 3986 and RFC 6874.
        // E.g., "[fe80::1]", "[fe80::1%25en0]", "[fe80::1]:80".
        let Some(close_bracket_idx) = host.rfind(']') else {
            return Err(errors::new("missing ']' in host"));
        };

        let colon_port = &host[close_bracket_idx + 1..];
        if !valid_optional_port(colon_port) {
            return Err(errors::errorf(
                format!("invalid port {} after host", strconv::quote(colon_port)),
                vec![],
            ));
        }
        let unescaped_colon_port = unescape(colon_port, ENCODE_HOST)?;

        let hostname = &host[1..close_bracket_idx];
        // RFC 6874 defines that %25 (%-encoded percent) introduces
        // the zone identifier, and the zone identifier can use basically
        // any %-encoding it likes. That's different from the host, which
        // can only %-encode non-ASCII bytes.
        // We do impose some restrictions on the zone, to avoid stupidity
        // like newlines.
        // PORT: the zone part starts with the '%' of "%25", so the join
        // cannot put invalid bytes next to each other.
        let unescaped_hostname = match hostname.find("%25") {
            Some(zone_idx) => {
                let host_part = unescape(&hostname[..zone_idx], ENCODE_HOST)?;
                let zone_part = unescape(&hostname[zone_idx..], ENCODE_ZONE)?;
                host_part + &zone_part
            }
            None => unescape(hostname, ENCODE_HOST)?,
        };

        // Per RFC 3986, only a host identified by a valid
        // IPv6 address can be enclosed by square brackets.
        // This excludes any IPv4, but notably not IPv4-mapped addresses.
        let addr = match netip::parse_addr(&unescaped_hostname) {
            Ok(addr) => addr,
            Err(err) => {
                return Err(errors::errorf(
                    format!("invalid host: {}", err.error()),
                    vec![err],
                ));
            }
        };
        if addr.is4() {
            return Err(errors::new("invalid IP-literal"));
        }
        return Ok(format!("[{unescaped_hostname}]{unescaped_colon_port}"));
    } else if let Some(i) = host.find(':') {
        let mut i = i;
        let last_colon = host.rfind(':').expect("contains ':'");
        if last_colon != i {
            // RFC 3986 does not allow colons to appear in the host subcomponent.
            //
            // However, a number of databases including PostgreSQL and MongoDB
            // permit a comma-separated list of hosts (with optional ports) in the
            // host subcomponent.
            //
            // Since we historically permitted colons to appear in the host,
            // enforce strict colons only for http and https URLs.
            //
            // See https://go.dev/issue/75223 and https://go.dev/issue/78077.
            if scheme == "http" || scheme == "https" {
                if urlstrictcolons_value() == "0" {
                    i = last_colon;
                }
            } else {
                i = last_colon;
            }
        }
        let colon_port = &host[i..];
        if !valid_optional_port(colon_port) {
            return Err(errors::errorf(
                format!("invalid port {} after host", strconv::quote(colon_port)),
                vec![],
            ));
        }
    }

    unescape(host, ENCODE_HOST)
}

impl URL {
    // Go: net/url/url.go:660 setPath
    /// setPath sets the Path and RawPath fields of the URL based on the provided
    /// escaped path p. It maintains the invariant that RawPath is only specified
    /// when it differs from the default encoding of the path.
    /// For example:
    /// - setPath("/foo/bar")   will set Path="/foo/bar" and RawPath=""
    /// - setPath("/foo%2fbar") will set Path="/foo/bar" and RawPath="/foo%2fbar"
    /// setPath will return an error only if the provided path contains an invalid
    /// escaping.
    pub fn set_path(&mut self, p: &str) -> Result<(), GoError> {
        let path = unescape(p, ENCODE_PATH)?;
        let escp = escape(&path, ENCODE_PATH);
        self.path = path;
        if p == escp {
            // Default encoding is fine.
            self.raw_path = String::new();
        } else {
            self.raw_path = p.to_string();
        }
        Ok(())
    }

    // Go: net/url/url.go:687 EscapedPath
    /// EscapedPath returns the escaped form of u.Path.
    /// In general there are multiple possible escaped forms of any path.
    /// EscapedPath returns u.RawPath when it is a valid escaping of u.Path.
    /// Otherwise EscapedPath ignores u.RawPath and computes an escaped
    /// form on its own.
    pub fn escaped_path(&self) -> String {
        if !self.raw_path.is_empty() && valid_encoded(&self.raw_path, ENCODE_PATH) {
            if let Ok(p) = unescape(&self.raw_path, ENCODE_PATH) {
                if p == self.path {
                    return self.raw_path.clone();
                }
            }
        }
        if self.path == "*" {
            return "*".to_string(); // don't escape (Issue 11202)
        }
        escape(&self.path, ENCODE_PATH)
    }

    // Go: net/url/url.go:727 setFragment
    /// setFragment is like setPath but for Fragment/RawFragment.
    fn set_fragment(&mut self, f: &str) -> Result<(), GoError> {
        let frag = unescape(f, ENCODE_FRAGMENT)?;
        let escf = escape(&frag, ENCODE_FRAGMENT);
        self.fragment = frag;
        if f == escf {
            // Default encoding is fine.
            self.raw_fragment = String::new();
        } else {
            self.raw_fragment = f.to_string();
        }
        Ok(())
    }

    // Go: net/url/url.go:750 EscapedFragment
    /// EscapedFragment returns the escaped form of u.Fragment.
    pub fn escaped_fragment(&self) -> String {
        if !self.raw_fragment.is_empty() && valid_encoded(&self.raw_fragment, ENCODE_FRAGMENT) {
            if let Ok(f) = unescape(&self.raw_fragment, ENCODE_FRAGMENT) {
                if f == self.fragment {
                    return self.raw_fragment.clone();
                }
            }
        }
        escape(&self.fragment, ENCODE_FRAGMENT)
    }
}

// Go: net/url/url.go:703 validEncoded
/// validEncoded reports whether s is a valid encoded path or fragment,
/// according to mode.
/// It must not contain any bytes that require escaping during encoding.
fn valid_encoded(s: &str, mode: Encoding) -> bool {
    for &c in s.as_bytes() {
        // RFC 3986, Appendix A.
        // pchar = unreserved / pct-encoded / sub-delims / ":" / "@".
        // shouldEscape is not quite compliant with the RFC,
        // so we check the sub-delims ourselves and let
        // shouldEscape handle the others.
        match c {
            b'!' | b'$' | b'&' | b'\'' | b'(' | b')' | b'*' | b'+' | b',' | b';' | b'=' | b':'
            | b'@' => {
                // ok
            }
            b'[' | b']' => {
                // ok - not specified in RFC 3986 but left alone by modern browsers
            }
            b'%' => {
                // ok - percent encoded, will decode
            }
            _ => {
                if should_escape(c, mode) {
                    return false;
                }
            }
        }
    }
    true
}

// Go: net/url/url.go:762 validOptionalPort
/// validOptionalPort reports whether port is either an empty string
/// or matches /^:\d*$/
fn valid_optional_port(port: &str) -> bool {
    if port.is_empty() {
        return true;
    }
    if !port.starts_with(':') {
        return false;
    }
    for b in port[1..].chars() {
        if !b.is_ascii_digit() {
            return false;
        }
    }
    true
}

// Go: net/url/url.go:1263 validUserinfo
/// validUserinfo reports whether s is a valid userinfo string per RFC 3986
/// Section 3.2.1.
/// It doesn't validate pct-encoded. The caller does that via func unescape.
fn valid_userinfo(s: &str) -> bool {
    for r in s.chars() {
        if r.is_ascii_uppercase() {
            continue;
        }
        if r.is_ascii_lowercase() {
            continue;
        }
        if r.is_ascii_digit() {
            continue;
        }
        match r {
            '-' | '.' | '_' | ':' | '~' | '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ','
            | ';' | '=' | '%' => continue,
            '@' => {
                // `RFC 3986 section 3.2.1` does not allow '@' in userinfo.
                // It is a delimiter between userinfo and host.
                // However, URLs are diverse, and in some cases,
                // the userinfo may contain an '@' character,
                // for example, in "http://username:p@ssword@google.com",
                // the string "username:p@ssword" should be treated as valid userinfo.
                // Ref:
                //   https://go.dev/issue/3439
                //   https://go.dev/issue/22655
                continue;
            }
            _ => return false,
        }
    }
    true
}

// Go: net/url/url.go:1297 stringContainsCTLByte
/// stringContainsCTLByte reports whether s contains any ASCII control character.
fn string_contains_ctl_byte(s: &str) -> bool {
    for &b in s.as_bytes() {
        if b < b' ' || b == 0x7f {
            return true;
        }
    }
    false
}

// Go: net/url/encoding_table.go:9 encoding
type Encoding = u8;

const ENCODE_PATH: Encoding = 1 << 0;
const ENCODE_PATH_SEGMENT: Encoding = 1 << 1;
const ENCODE_HOST: Encoding = 1 << 2;
const ENCODE_ZONE: Encoding = 1 << 3;
const ENCODE_USER_PASSWORD: Encoding = 1 << 4;
const ENCODE_QUERY_COMPONENT: Encoding = 1 << 5;
const ENCODE_FRAGMENT: Encoding = 1 << 6;
// hexChar is actually NOT an encoding mode, but there are only seven
// encoding modes. We might as well abuse the otherwise unused most
// significant bit in uint8 to indicate whether a character is
// hexadecimal.
const HEX_CHAR: Encoding = 1 << 7;

// Go: net/url/encoding_table.go:27 table
// Generated from the Go table: bit 0 encodePath, 1 encodePathSegment,
// 2 encodeHost, 3 encodeZone, 4 encodeUserPassword, 5 encodeQueryComponent,
// 6 encodeFragment, 7 hexChar. A set bit means the byte is left as is in
// that mode.
static TABLE: [Encoding; 256] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x4c, 0x0c, 0x00, 0x5f, 0x00, 0x5f, 0x0c, 0x4c, 0x4c, 0x4c, 0x5f, 0x5d, 0x7f, 0x7f, 0x41,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x4f, 0x5d, 0x0c, 0x5f, 0x0c, 0x40,
    0x43, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f,
    0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x0c, 0x00, 0x0c, 0x00, 0x7f,
    0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f,
    0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x00, 0x00, 0x00, 0x7f, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];
