#![allow(warnings)]

use crate::{
    error::{err, ErrorContext},
    fmt::{
        util::{
            fractional_time_to_nanos, fractional_time_to_span,
            parse_temporal_fraction,
        },
        Parsed,
    },
    util::{
        escape, parse,
        rangeint::{RFrom, TryRFrom},
        t,
        trie::{Trie, TrieNeedles},
    },
    Error, SignedDuration, Span, Unit,
};

/// TODO
#[derive(Clone, Debug)]
pub struct SpanParser {
    _private: (),
}

impl SpanParser {
    /// TODO
    pub fn new() -> SpanParser {
        SpanParser { _private: () }
    }

    /// TODO
    pub fn parse_span<I: AsRef<[u8]>>(&self, input: I) -> Result<Span, Error> {
        let input = input.as_ref();
        let parsed = self.parse_to_span(input).with_context(|| {
            err!(
                "failed to parse {input:?} in the \"friendly\" format",
                input = escape::Bytes(input)
            )
        })?;
        let span = parsed.into_full().with_context(|| {
            err!(
                "failed to parse {input:?} in the \"friendly\" format",
                input = escape::Bytes(input)
            )
        })?;
        Ok(span)
    }

    /// TODO
    pub fn parse_duration<I: AsRef<[u8]>>(
        &self,
        input: I,
    ) -> Result<SignedDuration, Error> {
        let input = input.as_ref();
        let parsed = self.parse_to_duration(input).with_context(|| {
            err!(
                "failed to parse {input:?} in the \"friendly\" format",
                input = escape::Bytes(input)
            )
        })?;
        let sdur = parsed.into_full().with_context(|| {
            err!(
                "failed to parse {input:?} in the \"friendly\" format",
                input = escape::Bytes(input)
            )
        })?;
        Ok(sdur)
    }

    #[inline(always)]
    fn parse_to_span<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, Span>, Error> {
        if input.is_empty() {
            return Err(err!("an empty string is not a valid duration"));
        }
        // Guard prefix sign parsing to avoid the function call, which is
        // marked unlineable to keep the fast path tighter.
        let (sign, input) =
            if !input.first().map_or(false, |&b| matches!(b, b'+' | b'-')) {
                (None, input)
            } else {
                let Parsed { value: sign, input } =
                    self.parse_prefix_sign(input);
                (sign, input)
            };

        let Parsed { value, input } = self.parse_unit_value(input)?;
        let Some(first_unit_value) = value else {
            return Err(err!(
                "parsing a friendly duration requires it to start \
                 with a unit value (a decimal integer) after an \
                 optional sign, but no integer was found",
            ));
        };
        let Parsed { value: span, input } =
            self.parse_units_to_span(input, first_unit_value)?;

        // As with the prefix sign parsing, guard it to avoid calling the
        // function.
        let (sign, input) = if !input.first().map_or(false, is_whitespace) {
            (sign.unwrap_or(t::Sign::N::<1>()), input)
        } else {
            let parsed = self.parse_suffix_sign(sign, input)?;
            (parsed.value, parsed.input)
        };
        Ok(Parsed { value: span * i64::from(sign.get()), input })
    }

    #[inline(always)]
    fn parse_to_duration<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, SignedDuration>, Error> {
        if input.is_empty() {
            return Err(err!("an empty string is not a valid duration"));
        }
        // Guard prefix sign parsing to avoid the function call, which is
        // marked unlineable to keep the fast path tighter.
        let (sign, input) =
            if !input.first().map_or(false, |&b| matches!(b, b'+' | b'-')) {
                (None, input)
            } else {
                let Parsed { value: sign, input } =
                    self.parse_prefix_sign(input);
                (sign, input)
            };

        let Parsed { value, input } = self.parse_unit_value(input)?;
        let Some(first_unit_value) = value else {
            return Err(err!(
                "parsing a friendly duration requires it to start \
                 with a unit value (a decimal integer) after an \
                 optional sign, but no integer was found",
            ));
        };
        let Parsed { value: nanos, input } =
            self.parse_units_to_duration(input, first_unit_value)?;

        // As with the prefix sign parsing, guard it to avoid calling the
        // function.
        let (sign, input) = if !input.first().map_or(false, is_whitespace) {
            (sign.unwrap_or(t::Sign::N::<1>()), input)
        } else {
            let parsed = self.parse_suffix_sign(sign, input)?;
            (parsed.value, parsed.input)
        };

        let nanos = nanos * sign;
        let secs = nanos / t::NANOS_PER_SECOND;
        let subsec_nanos = nanos % t::NANOS_PER_SECOND;
        let secs =
            t::NoUnits::try_rfrom("seconds", secs).with_context(|| {
                err!(
                    "parsed {nanos} nanoseconds, but overflows 64-bit seconds"
                )
            })?;
        let sdur = SignedDuration::new(secs.into(), subsec_nanos.into());
        Ok(Parsed { value: sdur, input })
    }

    #[inline(always)]
    fn parse_units_to_span<'i>(
        &self,
        mut input: &'i [u8],
        first_unit_value: t::NoUnits,
    ) -> Result<Parsed<'i, Span>, Error> {
        let mut parsed_any = false;
        let mut parsed_any_after_comma = true;
        let mut prev_unit: Option<Unit> = None;
        let mut value = first_unit_value;
        let mut span = Span::new();
        loop {
            let parsed = self.parse_hms_maybe(input, value)?;
            input = parsed.input;
            if let Some(hms) = parsed.value {
                if let Some(prev_unit) = prev_unit {
                    if prev_unit <= Unit::Hour {
                        return Err(err!(
                            "found 'HH:MM:SS' after unit {prev_unit}, \
                             but 'HH:MM:SS' can only appear after \
                             years, months, weeks or days",
                            prev_unit = prev_unit.singular(),
                        ));
                    }
                }
                span = set_span_unit_value(Unit::Hour, hms.hour, span)?;
                span = set_span_unit_value(Unit::Minute, hms.minute, span)?;
                span = if let Some(fraction) = hms.fraction {
                    fractional_time_to_span(
                        Unit::Second,
                        hms.second,
                        fraction,
                        span,
                    )?
                } else {
                    set_span_unit_value(Unit::Second, hms.second, span)?
                };
                parsed_any = true;
                break;
            }

            let fraction =
                if input.first().map_or(false, |&b| b == b'.' || b == b',') {
                    let parsed = parse_temporal_fraction(input)?;
                    input = parsed.input;
                    parsed.value
                } else {
                    None
                };

            // Eat any optional whitespace between the unit value and label.
            input = self.parse_optional_whitespace(input).input;

            // Parse the actual unit label/designator.
            let parsed = self.parse_unit_designator(input)?;
            input = parsed.input;
            let unit = parsed.value;

            // A comma is allowed to immediately follow the designator.
            // Since this is a rarer case, we guard it with a check to see
            // if the comma is there and only then call the function (which is
            // marked unlineable to try and keep the hot path tighter).
            if input.first().map_or(false, |&b| b == b',') {
                input = self.parse_optional_comma(input)?.input;
                parsed_any_after_comma = false;
            }

            if let Some(prev_unit) = prev_unit {
                if prev_unit <= unit {
                    return Err(err!(
                        "found value {value:?} with unit {unit} \
                         after unit {prev_unit}, but units must be \
                         written from largest to smallest \
                         (and they can't be repeated)",
                        unit = unit.singular(),
                        prev_unit = prev_unit.singular(),
                    ));
                }
            }
            prev_unit = Some(unit);
            parsed_any = true;

            if let Some(fraction) = fraction {
                span = fractional_time_to_span(unit, value, fraction, span)?;
                // Once we see a fraction, we are done. We don't permit parsing
                // any more units. That is, a fraction can only occur on the
                // lowest unit of time.
                break;
            } else {
                span = set_span_unit_value(unit, value, span)?;
            }

            // Eat any optional whitespace after the designator (or comma) and
            // before the next unit value. But if we don't see a unit value,
            // we don't eat the whitespace.
            let after_whitespace = self.parse_optional_whitespace(input).input;
            let parsed = self.parse_unit_value(after_whitespace)?;
            value = match parsed.value {
                None => break,
                Some(value) => value,
            };
            input = parsed.input;
            parsed_any_after_comma = true;
        }
        if !parsed_any_after_comma {
            return Err(err!(
                "found comma at the end of duration, \
                 but a comma indicates at least one more \
                 unit follows and none were found after \
                 {prev_unit}",
                // OK because parsed_any_after_comma can only
                // be false when prev_unit is set.
                prev_unit = prev_unit.unwrap().plural(),
            ));
        }
        if !parsed_any {
            return Err(err!(
                "expected to find at least one unit value with a \
                 designator label, but none were found",
            ));
        }
        Ok(Parsed { value: span, input })
    }

    #[inline(always)]
    fn parse_units_to_duration<'i>(
        &self,
        mut input: &'i [u8],
        first_unit_value: t::NoUnits,
    ) -> Result<Parsed<'i, t::NoUnits128>, Error> {
        let mut parsed_any = false;
        let mut parsed_any_after_comma = true;
        let mut prev_unit: Option<Unit> = None;
        let mut value = first_unit_value;
        let mut nanos = t::NoUnits128::N::<0>();
        loop {
            let parsed = self.parse_hms_maybe(input, value)?;
            input = parsed.input;
            if let Some(hms) = parsed.value {
                if let Some(prev_unit) = prev_unit {
                    if prev_unit <= Unit::Hour {
                        return Err(err!(
                            "found 'HH:MM:SS' after unit {prev_unit}, \
                             but 'HH:MM:SS' can only appear after \
                             years, months, weeks or days",
                            prev_unit = prev_unit.singular(),
                        ));
                    }
                }
                nanos += nanos_unit_value(Unit::Hour, hms.hour)?;
                nanos += nanos_unit_value(Unit::Minute, hms.minute)?;
                nanos += nanos_unit_value(Unit::Second, hms.second)?;
                if let Some(fraction) = hms.fraction {
                    nanos += fractional_time_to_nanos(Unit::Second, fraction);
                };
                parsed_any = true;
                break;
            }

            let fraction =
                if input.first().map_or(false, |&b| b == b'.' || b == b',') {
                    let parsed = parse_temporal_fraction(input)?;
                    input = parsed.input;
                    parsed.value
                } else {
                    None
                };

            // Eat any optional whitespace between the unit value and label.
            input = self.parse_optional_whitespace(input).input;

            // Parse the actual unit label/designator.
            let parsed = self.parse_unit_designator(input)?;
            input = parsed.input;
            let unit = parsed.value;

            // A comma is allowed to immediately follow the designator.
            // Since this is a rarer case, we guard it with a check to see
            // if the comma is there and only then call the function (which is
            // marked unlineable to try and keep the hot path tighter).
            if input.first().map_or(false, |&b| b == b',') {
                input = self.parse_optional_comma(input)?.input;
                parsed_any_after_comma = false;
            }

            if let Some(prev_unit) = prev_unit {
                if prev_unit <= unit {
                    return Err(err!(
                        "found value {value:?} with unit {unit} \
                         after unit {prev_unit}, but units must be \
                         written from largest to smallest \
                         (and they can't be repeated)",
                        unit = unit.singular(),
                        prev_unit = prev_unit.singular(),
                    ));
                }
            }
            prev_unit = Some(unit);
            parsed_any = true;

            nanos += nanos_unit_value(unit, value)?;
            if let Some(fraction) = fraction {
                nanos += fractional_time_to_nanos(unit, fraction);
                // Once we see a fraction, we are done. We don't permit parsing
                // any more units. That is, a fraction can only occur on the
                // lowest unit of time.
                break;
            }

            // Eat any optional whitespace after the designator (or comma) and
            // before the next unit value. But if we don't see a unit value,
            // we don't eat the whitespace.
            let after_whitespace = self.parse_optional_whitespace(input).input;
            let parsed = self.parse_unit_value(after_whitespace)?;
            value = match parsed.value {
                None => break,
                Some(value) => value,
            };
            input = parsed.input;
            parsed_any_after_comma = true;
        }
        if !parsed_any_after_comma {
            return Err(err!(
                "found comma at the end of duration, \
                 but a comma indicates at least one more \
                 unit follows and none were found after \
                 {prev_unit}",
                // OK because parsed_any_after_comma can only
                // be false when prev_unit is set.
                prev_unit = prev_unit.unwrap().plural(),
            ));
        }
        if !parsed_any {
            return Err(err!(
                "expected to find at least one unit value with a \
                 designator label, but none were found",
            ));
        }
        Ok(Parsed { value: nanos, input })
    }

    /// This possibly parses a `HH:MM:SS[.fraction]`.
    ///
    /// This expects that a unit value has been parsed and looks for a `:`
    /// at `input[0]`. If `:` is found, then this proceeds to parse HMS.
    /// Otherwise, a `None` value is returned.
    #[inline(always)]
    fn parse_hms_maybe<'i>(
        &self,
        mut input: &'i [u8],
        hour: t::NoUnits,
    ) -> Result<Parsed<'i, Option<HMS>>, Error> {
        if !input.first().map_or(false, |&b| b == b':') {
            return Ok(Parsed { input, value: None });
        }
        let Parsed { input, value } = self.parse_hms(&input[1..], hour)?;
        Ok(Parsed { input, value: Some(value) })
    }

    /// This parses a `HH:MM:SS[.fraction]` when it is known/expected to be
    /// present.
    ///
    /// This is also marked as non-inlined since we expect this to be a
    /// less common case. Where as `parse_hms_maybe` is called unconditionally
    /// to check to see if the HMS should be parsed.
    ///
    /// This assumes that the beginning of `input` immediately follows the
    /// first `:` in `HH:MM:SS[.fraction]`.
    #[inline(never)]
    fn parse_hms<'i>(
        &self,
        mut input: &'i [u8],
        hour: t::NoUnits,
    ) -> Result<Parsed<'i, HMS>, Error> {
        let Parsed { input, value } = self.parse_unit_value(input)?;
        let Some(minute) = value else {
            return Err(err!(
                "expected to parse minute in 'HH:MM:SS' format \
                 following parsed hour of {hour}",
            ));
        };
        if !input.first().map_or(false, |&b| b == b':') {
            return Err(err!(
                "when parsing 'HH:MM:SS' format, expected to \
                 see a ':' after the parsed minute of {minute}",
            ));
        }
        let input = &input[1..];
        let Parsed { input, value } = self.parse_unit_value(input)?;
        let Some(second) = value else {
            return Err(err!(
                "expected to parse second in 'HH:MM:SS' format \
                 following parsed minute of {minute}",
            ));
        };
        let (fraction, input) =
            if input.first().map_or(false, |&b| b == b'.' || b == b',') {
                let parsed = parse_temporal_fraction(input)?;
                (parsed.value, parsed.input)
            } else {
                (None, input)
            };
        let hms = HMS { hour, minute, second, fraction };
        Ok(Parsed { input, value: hms })
    }

    /// Parsed a unit value, i.e., an integer.
    ///
    /// If no digits (`[0-9]`) were found at the current position of the parser
    /// then `None` is returned. This means, for example, that parsing a
    /// duration should stop.
    ///
    /// Note that this is safe to call on untrusted input. It will not attempt
    /// to consume more input than could possibly fit into a parsed integer.
    #[inline(always)]
    fn parse_unit_value<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, Option<t::NoUnits>>, Error> {
        // Discovered via `i64::MAX.to_string().len()`.
        const MAX_I64_DIGITS: usize = 19;

        let mkdigits = parse::slicer(input);
        while mkdigits(input).len() <= MAX_I64_DIGITS
            && input.first().map_or(false, u8::is_ascii_digit)
        {
            input = &input[1..];
        }
        let digits = mkdigits(input);
        if digits.is_empty() {
            return Ok(Parsed { value: None, input });
        }
        let value = parse::i64(digits).with_context(|| {
            err!(
                "failed to parse {digits:?} as 64-bit signed integer",
                digits = escape::Bytes(digits),
            )
        })?;
        // OK because t::NoUnits permits all possible i64 values.
        let value = t::NoUnits::new(value).unwrap();
        Ok(Parsed { value: Some(value), input })
    }

    /// Parse a unit designator, e.g., `years` or `nano`.
    ///
    /// If no designator could be found, including if the given `input` is
    /// empty, then this return an error.
    ///
    /// This does not attempt to handle leading or trailing whitespace.
    #[inline(always)]
    fn parse_unit_designator<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, Unit>, Error> {
        if input.is_empty() {
            return Err(err!(
                "expected to find unit designator suffix \
                 (e.g., 'years' or 'secs'), \
                 but found end of input",
            ));
        }
        let Some((unit, len)) = DESIGNATOR_TRIE.find(input) else {
            return Err(err!(
                "expected to find unit designator suffix \
                 (e.g., 'years' or 'secs'), \
                 but found input beginning with {found:?} instead",
                found = escape::Bytes(&input[..input.len().min(15)]),
            ));
        };
        Ok(Parsed { value: unit, input: &input[len..] })
    }

    /// Parses an optional prefix sign from the given input.
    ///
    /// A prefix sign is either a `+` or a `-`. If neither are found, then
    /// `None` is returned.
    #[inline(never)]
    fn parse_prefix_sign<'i>(
        &self,
        input: &'i [u8],
    ) -> Parsed<'i, Option<t::Sign>> {
        let Some(sign) = input.first().copied() else {
            return Parsed { value: None, input };
        };
        let sign = if sign == b'+' {
            t::Sign::N::<1>()
        } else if sign == b'-' {
            t::Sign::N::<-1>()
        } else {
            return Parsed { value: None, input };
        };
        Parsed { value: Some(sign), input: &input[1..] }
    }

    /// Parses an optional suffix sign from the given input.
    ///
    /// This requires, as input, the result of parsing a prefix sign since this
    /// will return an error if both a prefix and a suffix sign were found.
    ///
    /// A suffix sign is the string `ago`. Any other string means that there is
    /// no suffix sign. This will also look for mandatory whitespace and eat
    /// any additional optional whitespace. i.e., This should be called
    /// immediately after parsing the last unit designator/label.
    ///
    /// Regardless of whether a prefix or suffix sign was found, a definitive
    /// sign is returned. (When there's no prefix or suffix sign, then the sign
    /// returned is positive.)
    #[inline(never)]
    fn parse_suffix_sign<'i>(
        &self,
        prefix_sign: Option<t::Sign>,
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, t::Sign>, Error> {
        if !input.first().map_or(false, is_whitespace) {
            let sign = prefix_sign.unwrap_or(t::Sign::N::<1>());
            return Ok(Parsed { value: sign, input });
        }
        // Eat any additional whitespace we find before looking for 'ago'.
        input = self.parse_optional_whitespace(&input[1..]).input;
        let (suffix_sign, input) = if input.starts_with(b"ago") {
            (Some(t::Sign::N::<-1>()), &input[3..])
        } else {
            (None, input)
        };
        let sign = match (prefix_sign, suffix_sign) {
            (Some(_), Some(_)) => {
                return Err(err!(
                    "expected to find either a prefix sign (+/-) or \
                     a suffix sign (ago), but found both",
                ))
            }
            (Some(sign), None) => sign,
            (None, Some(sign)) => sign,
            (None, None) => t::Sign::N::<1>(),
        };
        Ok(Parsed { value: sign, input })
    }

    /// Parses an optional comma following a unit designator.
    ///
    /// If a comma is seen, then it is mandatory that it be followed by
    /// whitespace.
    ///
    /// This also takes care to provide a custom error message if the end of
    /// input is seen after a comma.
    ///
    /// If `input` doesn't start with a comma, then this is a no-op.
    #[inline(never)]
    fn parse_optional_comma<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, ()>, Error> {
        if !input.first().map_or(false, |&b| b == b',') {
            return Ok(Parsed { value: (), input });
        }
        input = &input[1..];
        if input.is_empty() {
            return Err(err!(
                "expected whitespace after comma, but found end of input"
            ));
        }
        if !is_whitespace(&input[0]) {
            return Err(err!(
                "expected whitespace after comma, but found {found:?}",
                found = escape::Byte(input[0]),
            ));
        }
        Ok(Parsed { value: (), input: &input[1..] })
    }

    /// Parses one or more bytes of ASCII whitespace.
    ///
    /// If whitespace was not found at the beginning of `input`, then an error
    /// is returned.
    #[inline(always)]
    fn parse_required_whitespace<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, ()>, Error> {
        if input.is_empty() {
            return Err(err!("expected whitespace, but found end of input"));
        }
        if !is_whitespace(&input[0]) {
            return Err(err!(
                "expected whitespace, but found {found:?}",
                found = escape::Byte(input[0]),
            ));
        }
        Ok(self.parse_optional_whitespace(&input[1..]))
    }

    /// Parses zero or more bytes of ASCII whitespace.
    #[inline(always)]
    fn parse_optional_whitespace<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Parsed<'i, ()> {
        while input.first().map_or(false, is_whitespace) {
            input = &input[1..];
        }
        Parsed { value: (), input }
    }
}

/// A type that represents the parsed components of `HH:MM:SS[.fraction]`.
#[derive(Debug)]
struct HMS {
    hour: t::NoUnits,
    minute: t::NoUnits,
    second: t::NoUnits,
    fraction: Option<t::SubsecNanosecond>,
}

/// Set the given unit to the given value on the given span.
///
/// If the value outside the legal boundaries for the given unit, then an error
/// is returned.
fn set_span_unit_value(
    unit: Unit,
    value: t::NoUnits,
    mut span: Span,
) -> Result<Span, Error> {
    if unit <= Unit::Hour {
        let result = span.try_units_ranged(unit, value).with_context(|| {
            err!(
                "failed to set value {value:?} \
                 as {unit} unit on span",
                unit = Unit::from(unit).singular(),
            )
        });
        // This is annoying, but because we can write out a larger
        // number of hours/minutes/seconds than what we actually
        // support, we need to be prepared to parse an unbalanced span
        // if our time units are too big here.
        span = match result {
            Ok(span) => span,
            Err(_) => fractional_time_to_span(
                unit,
                value,
                t::SubsecNanosecond::N::<0>(),
                span,
            )?,
        };
    } else {
        span = span.try_units_ranged(unit, value).with_context(|| {
            err!(
                "failed to set value {value:?} \
                 as {unit} unit on span",
                unit = Unit::from(unit).singular(),
            )
        })?;
    }
    Ok(span)
}

/// Returns the given parsed value, interpreted as the given unit, in units of
/// nanoseconds.
///
/// If the given unit is not supported for signed durations (i.e., calendar
/// units), then an error is returned.
fn nanos_unit_value(
    unit: Unit,
    value: t::NoUnits,
) -> Result<t::NoUnits128, Error> {
    let value = t::NoUnits128::rfrom(value);
    // Convert our parsed unit into a number of nanoseconds.
    //
    // Note also that overflow isn't possible here, since all of our parsed
    // values are guaranteed to fit into i64, but we accrue into an i128.
    // Of course, the final i128 might overflow a SignedDuration, but this
    // is checked once at the end of parsing when a SignedDuration is
    // materialized.
    let unit_nanos = match unit {
        Unit::Hour => value * t::NANOS_PER_HOUR,
        Unit::Minute => value * t::NANOS_PER_MINUTE,
        Unit::Second => value * t::NANOS_PER_SECOND,
        Unit::Millisecond => value * t::NANOS_PER_MILLI,
        Unit::Microsecond => value * t::NANOS_PER_MICRO,
        Unit::Nanosecond => value,
        unsupported => {
            return Err(err!(
                "parsing {unit} units into a `SignedDuration` is not supported \
                 (perhaps try parsing into a `Span` instead)",
                unit = unsupported.singular(),
            ));
        }
    };
    Ok(unit_nanos)
}

/// Returns true if the byte is ASCII whitespace.
fn is_whitespace(byte: &u8) -> bool {
    matches!(*byte, b' ' | b'\t' | b'\n' | b'\r' | b'\x0C')
}

/// The type for a `const` trie for parsing a "friendly" unit designator.
///
/// This doesn't just recognize the name, it also maps it to its corresponding
/// `Unit` variant value.
type DesignatorTrie = Trie<98, { DESIGNATOR_NEEDLES.alphabet_len() }, Unit>;

/// A static corresponding to the trie.
///
/// This ensures it's only created once (at compile time) and that we don't
/// get multiple copies of it embedded into the binary.
static DESIGNATOR_TRIE: &'static DesignatorTrie =
    &Trie::new(&DESIGNATOR_NEEDLES);

/// The needle-to-unit map.
///
/// We give this an intermediate name (and it has to be `const`) so that we
/// can query it's alphabet length in the definition of the `Trie` type. (Its
/// alphabet length is actually much smaller than the number of distinct `u8`
/// values.)
const DESIGNATOR_NEEDLES: TrieNeedles<Unit> = TrieNeedles::new(&[
    ("years", Unit::Year),
    ("year", Unit::Year),
    ("yrs", Unit::Year),
    ("yr", Unit::Year),
    ("y", Unit::Year),
    ("months", Unit::Month),
    ("month", Unit::Month),
    ("mos", Unit::Month),
    ("mo", Unit::Month),
    ("weeks", Unit::Week),
    ("week", Unit::Week),
    ("wks", Unit::Week),
    ("wk", Unit::Week),
    ("w", Unit::Week),
    ("days", Unit::Day),
    ("day", Unit::Day),
    ("d", Unit::Day),
    ("hours", Unit::Hour),
    ("hour", Unit::Hour),
    ("hrs", Unit::Hour),
    ("hr", Unit::Hour),
    ("h", Unit::Hour),
    ("minutes", Unit::Minute),
    ("minute", Unit::Minute),
    ("mins", Unit::Minute),
    ("min", Unit::Minute),
    ("m", Unit::Minute),
    ("seconds", Unit::Second),
    ("second", Unit::Second),
    ("secs", Unit::Second),
    ("sec", Unit::Second),
    ("s", Unit::Second),
    ("milliseconds", Unit::Millisecond),
    ("millisecond", Unit::Millisecond),
    ("millis", Unit::Millisecond),
    ("milli", Unit::Millisecond),
    ("msecs", Unit::Millisecond),
    ("msec", Unit::Millisecond),
    ("ms", Unit::Millisecond),
    ("microseconds", Unit::Microsecond),
    ("microsecond", Unit::Microsecond),
    ("micros", Unit::Microsecond),
    ("micro", Unit::Microsecond),
    ("usecs", Unit::Microsecond),
    ("usec", Unit::Microsecond),
    ("µsecs", Unit::Microsecond),
    ("µsec", Unit::Microsecond),
    ("us", Unit::Microsecond),
    ("µs", Unit::Microsecond),
    ("nanoseconds", Unit::Nanosecond),
    ("nanosecond", Unit::Nanosecond),
    ("nanos", Unit::Nanosecond),
    ("nano", Unit::Nanosecond),
    ("nsecs", Unit::Nanosecond),
    ("nsec", Unit::Nanosecond),
    ("ns", Unit::Nanosecond),
]);

#[cfg(test)]
mod tests {
    use crate::ToSpan;

    use super::*;

    #[test]
    fn parse_unit_designator() {
        let p = SpanParser::new();
        dbg!(p.parse_unit_designator(b"years"));
    }

    #[test]
    fn parse_span_basic() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap();

        insta::assert_snapshot!(p("5 years"), @"P5y");
        insta::assert_snapshot!(p("5 years 4 months"), @"P5y4m");
        insta::assert_snapshot!(p("5 years 4 months 3 hours"), @"P5y4mT3h");
        insta::assert_snapshot!(p("5 years, 4 months, 3 hours"), @"P5y4mT3h");

        insta::assert_snapshot!(p("01:02:03"), @"PT1h2m3s");
        insta::assert_snapshot!(p("5 days 01:02:03"), @"P5dT1h2m3s");
        // This is Python's `str(timedelta)` format!
        insta::assert_snapshot!(p("5 days, 01:02:03"), @"P5dT1h2m3s");
        insta::assert_snapshot!(p("3yrs 5 days 01:02:03"), @"P3y5dT1h2m3s");
        insta::assert_snapshot!(p("3yrs 5 days, 01:02:03"), @"P3y5dT1h2m3s");
        insta::assert_snapshot!(
            p("3yrs 5 days, 01:02:03.123456789"),
            @"P3y5dT1h2m3.123456789s",
        );
        insta::assert_snapshot!(p("999:999:999"), @"PT999h999m999s");
    }

    #[test]
    fn parse_span_fractional() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap();

        insta::assert_snapshot!(p("1.5hrs"), @"PT1h30m");
        insta::assert_snapshot!(p("1.5mins"), @"PT1m30s");
        insta::assert_snapshot!(p("1.5secs"), @"PT1.5s");
        insta::assert_snapshot!(p("1.5msecs"), @"PT0.0015s");
        insta::assert_snapshot!(p("1.5µsecs"), @"PT0.0000015s");

        insta::assert_snapshot!(p("1d 1.5hrs"), @"P1dT1h30m");
        insta::assert_snapshot!(p("1h 1.5mins"), @"PT1h1m30s");
        insta::assert_snapshot!(p("1m 1.5secs"), @"PT1m1.5s");
        insta::assert_snapshot!(p("1s 1.5msecs"), @"PT1.0015s");
        insta::assert_snapshot!(p("1ms 1.5µsecs"), @"PT0.0010015s");

        insta::assert_snapshot!(p("1s2000ms"), @"PT3s");
    }

    #[test]
    fn parse_span_boundaries() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap();

        insta::assert_snapshot!(p("19998 years"), @"P19998y");
        insta::assert_snapshot!(p("19998 years ago"), @"-P19998y");
        insta::assert_snapshot!(p("239976 months"), @"P239976m");
        insta::assert_snapshot!(p("239976 months ago"), @"-P239976m");
        insta::assert_snapshot!(p("1043497 weeks"), @"P1043497w");
        insta::assert_snapshot!(p("1043497 weeks ago"), @"-P1043497w");
        insta::assert_snapshot!(p("7304484 days"), @"P7304484d");
        insta::assert_snapshot!(p("7304484 days ago"), @"-P7304484d");
        insta::assert_snapshot!(p("175307616 hours"), @"PT175307616h");
        insta::assert_snapshot!(p("175307616 hours ago"), @"-PT175307616h");
        insta::assert_snapshot!(p("10518456960 minutes"), @"PT10518456960m");
        insta::assert_snapshot!(p("10518456960 minutes ago"), @"-PT10518456960m");
        insta::assert_snapshot!(p("631107417600 seconds"), @"PT631107417600s");
        insta::assert_snapshot!(p("631107417600 seconds ago"), @"-PT631107417600s");
        insta::assert_snapshot!(p("631107417600000 milliseconds"), @"PT631107417600s");
        insta::assert_snapshot!(p("631107417600000 milliseconds ago"), @"-PT631107417600s");
        insta::assert_snapshot!(p("631107417600000000 microseconds"), @"PT631107417600s");
        insta::assert_snapshot!(p("631107417600000000 microseconds ago"), @"-PT631107417600s");
        insta::assert_snapshot!(p("9223372036854775807 nanoseconds"), @"PT9223372036.854775807s");
        insta::assert_snapshot!(p("9223372036854775807 nanoseconds ago"), @"-PT9223372036.854775807s");

        insta::assert_snapshot!(p("175307617 hours"), @"PT175307616h60m");
        insta::assert_snapshot!(p("175307617 hours ago"), @"-PT175307616h60m");
        insta::assert_snapshot!(p("10518456961 minutes"), @"PT10518456960m60s");
        insta::assert_snapshot!(p("10518456961 minutes ago"), @"-PT10518456960m60s");
        insta::assert_snapshot!(p("631107417601 seconds"), @"PT631107417601s");
        insta::assert_snapshot!(p("631107417601 seconds ago"), @"-PT631107417601s");
        insta::assert_snapshot!(p("631107417600001 milliseconds"), @"PT631107417600.001s");
        insta::assert_snapshot!(p("631107417600001 milliseconds ago"), @"-PT631107417600.001s");
        insta::assert_snapshot!(p("631107417600000001 microseconds"), @"PT631107417600.000001s");
        insta::assert_snapshot!(p("631107417600000001 microseconds ago"), @"-PT631107417600.000001s");
        // We don't include nanoseconds here, because that will fail to
        // parse due to overflowing i64.
    }

    #[test]
    fn err_span_basic() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap_err();

        insta::assert_snapshot!(
            p(""),
            @r###"failed to parse "" in the "friendly" format: an empty string is not a valid duration"###,
        );
        insta::assert_snapshot!(
            p(" "),
            @r###"failed to parse " " in the "friendly" format: parsing a friendly duration requires it to start with a unit value (a decimal integer) after an optional sign, but no integer was found"###,
        );
        insta::assert_snapshot!(
            p("a"),
            @r###"failed to parse "a" in the "friendly" format: parsing a friendly duration requires it to start with a unit value (a decimal integer) after an optional sign, but no integer was found"###,
        );
        insta::assert_snapshot!(
            p("2 months 1 year"),
            @r###"failed to parse "2 months 1 year" in the "friendly" format: found value 1 with unit year after unit month, but units must be written from largest to smallest (and they can't be repeated)"###,
        );
        insta::assert_snapshot!(
            p("1 year 1 mont"),
            @r###"failed to parse "1 year 1 mont" in the "friendly" format: parsed value 'P1y1m', but unparsed input "nt" remains (expected no unparsed input)"###,
        );
        insta::assert_snapshot!(
            p("2 months,"),
            @r###"failed to parse "2 months," in the "friendly" format: expected whitespace after comma, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("2 months, "),
            @r###"failed to parse "2 months, " in the "friendly" format: found comma at the end of duration, but a comma indicates at least one more unit follows and none were found after months"###,
        );
        insta::assert_snapshot!(
            p("2 months ,"),
            @r###"failed to parse "2 months ," in the "friendly" format: parsed value 'P2m', but unparsed input "," remains (expected no unparsed input)"###,
        );
    }

    #[test]
    fn err_span_sign() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap_err();

        insta::assert_snapshot!(
            p("1 year 1 monthago"),
            @r###"failed to parse "1 year 1 monthago" in the "friendly" format: parsed value 'P1y1m', but unparsed input "ago" remains (expected no unparsed input)"###,
        );
        insta::assert_snapshot!(
            p("+1 year 1 month ago"),
            @r###"failed to parse "+1 year 1 month ago" in the "friendly" format: expected to find either a prefix sign (+/-) or a suffix sign (ago), but found both"###,
        );
        insta::assert_snapshot!(
            p("-1 year 1 month ago"),
            @r###"failed to parse "-1 year 1 month ago" in the "friendly" format: expected to find either a prefix sign (+/-) or a suffix sign (ago), but found both"###,
        );
    }

    #[test]
    fn err_span_overflow_fraction() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap_err();

        insta::assert_snapshot!(
            // One fewer micro, and this parses okay. The error occurs because
            // the maximum number of microseconds is subtracted off, and we're
            // left over with a value that overflows an i64.
            p("640330789636854776 micros"),
            @r###"failed to parse "640330789636854776 micros" in the "friendly" format: failed to set nanosecond value 9223372036854776000 on span determined from 640330789636854776.0: parameter 'nanoseconds' with value 9223372036854776000 is not in the required range of -9223372036854775807..=9223372036854775807"###,
        );
        insta::assert_snapshot!(
            // This is like the test above, but actually exercises a slightly
            // different error path by using an explicit fraction. Here, if
            // we had x.807 micros, it would parse successfully.
            p("640330789636854775.808 micros"),
            @r###"failed to parse "640330789636854775.808 micros" in the "friendly" format: failed to set nanosecond value 9223372036854775808 on span determined from 640330789636854775.808000000: parameter 'nanoseconds' with value 9223372036854775808 is not in the required range of -9223372036854775807..=9223372036854775807"###,
        );
    }

    #[test]
    fn err_span_overflow_units() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap_err();

        insta::assert_snapshot!(
            p("19999 years"),
            @r###"failed to parse "19999 years" in the "friendly" format: failed to set value 19999 as year unit on span: parameter 'years' with value 19999 is not in the required range of -19998..=19998"###,
        );
        insta::assert_snapshot!(
            p("19999 years ago"),
            @r###"failed to parse "19999 years ago" in the "friendly" format: failed to set value 19999 as year unit on span: parameter 'years' with value 19999 is not in the required range of -19998..=19998"###,
        );

        insta::assert_snapshot!(
            p("239977 months"),
            @r###"failed to parse "239977 months" in the "friendly" format: failed to set value 239977 as month unit on span: parameter 'months' with value 239977 is not in the required range of -239976..=239976"###,
        );
        insta::assert_snapshot!(
            p("239977 months ago"),
            @r###"failed to parse "239977 months ago" in the "friendly" format: failed to set value 239977 as month unit on span: parameter 'months' with value 239977 is not in the required range of -239976..=239976"###,
        );

        insta::assert_snapshot!(
            p("1043498 weeks"),
            @r###"failed to parse "1043498 weeks" in the "friendly" format: failed to set value 1043498 as week unit on span: parameter 'weeks' with value 1043498 is not in the required range of -1043497..=1043497"###,
        );
        insta::assert_snapshot!(
            p("1043498 weeks ago"),
            @r###"failed to parse "1043498 weeks ago" in the "friendly" format: failed to set value 1043498 as week unit on span: parameter 'weeks' with value 1043498 is not in the required range of -1043497..=1043497"###,
        );

        insta::assert_snapshot!(
            p("7304485 days"),
            @r###"failed to parse "7304485 days" in the "friendly" format: failed to set value 7304485 as day unit on span: parameter 'days' with value 7304485 is not in the required range of -7304484..=7304484"###,
        );
        insta::assert_snapshot!(
            p("7304485 days ago"),
            @r###"failed to parse "7304485 days ago" in the "friendly" format: failed to set value 7304485 as day unit on span: parameter 'days' with value 7304485 is not in the required range of -7304484..=7304484"###,
        );

        insta::assert_snapshot!(
            p("9223372036854775808 nanoseconds"),
            @r###"failed to parse "9223372036854775808 nanoseconds" in the "friendly" format: failed to parse "9223372036854775808" as 64-bit signed integer: number '9223372036854775808' too big to parse into 64-bit integer"###,
        );
        insta::assert_snapshot!(
            p("9223372036854775808 nanoseconds ago"),
            @r###"failed to parse "9223372036854775808 nanoseconds ago" in the "friendly" format: failed to parse "9223372036854775808" as 64-bit signed integer: number '9223372036854775808' too big to parse into 64-bit integer"###,
        );
    }

    #[test]
    fn err_span_fraction() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap_err();

        insta::assert_snapshot!(
            p("1.5 years"),
            @r###"failed to parse "1.5 years" in the "friendly" format: fractional year units are not allowed"###,
        );
        insta::assert_snapshot!(
            p("1.5 nanos"),
            @r###"failed to parse "1.5 nanos" in the "friendly" format: fractional nanosecond units are not allowed"###,
        );
    }

    #[test]
    fn err_span_hms() {
        let p = |s: &str| SpanParser::new().parse_span(s).unwrap_err();

        insta::assert_snapshot!(
            p("05:"),
            @r###"failed to parse "05:" in the "friendly" format: expected to parse minute in 'HH:MM:SS' format following parsed hour of 5"###,
        );
        insta::assert_snapshot!(
            p("05:06"),
            @r###"failed to parse "05:06" in the "friendly" format: when parsing 'HH:MM:SS' format, expected to see a ':' after the parsed minute of 6"###,
        );
        insta::assert_snapshot!(
            p("05:06:"),
            @r###"failed to parse "05:06:" in the "friendly" format: expected to parse second in 'HH:MM:SS' format following parsed minute of 6"###,
        );
        insta::assert_snapshot!(
            p("2 hours, 05:06:07"),
            @r###"failed to parse "2 hours, 05:06:07" in the "friendly" format: found 'HH:MM:SS' after unit hour, but 'HH:MM:SS' can only appear after years, months, weeks or days"###,
        );
    }

    #[test]
    fn parse_duration_basic() {
        let p = |s: &str| SpanParser::new().parse_duration(s).unwrap();

        insta::assert_snapshot!(p("1 hour, 2 minutes, 3 seconds"), @"PT1h2m3s");
        insta::assert_snapshot!(p("01:02:03"), @"PT1h2m3s");
        insta::assert_snapshot!(p("999:999:999"), @"PT1015h55m39s");
    }

    #[test]
    fn parse_duration_fractional() {
        let p = |s: &str| SpanParser::new().parse_duration(s).unwrap();

        insta::assert_snapshot!(p("1.5hrs"), @"PT1h30m");
        insta::assert_snapshot!(p("1.5mins"), @"PT1m30s");
        insta::assert_snapshot!(p("1.5secs"), @"PT1.5s");
        insta::assert_snapshot!(p("1.5msecs"), @"PT0.0015s");
        insta::assert_snapshot!(p("1.5µsecs"), @"PT0.0000015s");

        insta::assert_snapshot!(p("1h 1.5mins"), @"PT1h1m30s");
        insta::assert_snapshot!(p("1m 1.5secs"), @"PT1m1.5s");
        insta::assert_snapshot!(p("1s 1.5msecs"), @"PT1.0015s");
        insta::assert_snapshot!(p("1ms 1.5µsecs"), @"PT0.0010015s");

        insta::assert_snapshot!(p("1s2000ms"), @"PT3s");
    }
}
