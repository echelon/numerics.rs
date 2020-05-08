// Copyright (c) 2016, 2020 Brandon Thomas <bt@brand.io>

#![deny(dead_code)]
#![deny(missing_docs)]
#![deny(unreachable_patterns)]
#![deny(unused_extern_crates)]
#![deny(unused_imports)]
#![deny(unused_qualifications)]

//! **Numerics**, a library for converting numbers to their English word readings.
//!
//! Usage:
//!
//! ```rust
//! use numerics::Numerics;
//!
//! let converter = Numerics::builder().set_custom_negative_word(Some("minus")).build();
//!
//! assert_eq!(converter.convert_number(123).unwrap(),
//!   vec!["one".to_string(), "hundred".to_string(), "twenty".to_string(), "three".to_string()]);
//! ```

pub use num::Integer;
pub use num::{Num, NumCast, ToPrimitive, PrimInt};
pub use num::traits::AsPrimitive;

const NEGATIVE: &'static str = "negative";

const BASE_NUMBERS: [&'static str; 20] = [
  "zero",
  "one",
  "two",
  "three",
  "four",
  "five",
  "six",
  "seven",
  "eight",
  "nine",
  "ten",
  "eleven",
  "twelve",
  "thirteen",
  "fourteen",
  "fifteen",
  "sixteen",
  "seventeen",
  "eighteen",
  "nineteen",
];

const TENS: [&'static str; 8] = [
  "twenty",
  "thirty",
  "forty",
  "fifty",
  "sixty",
  "seventy",
  "eighty",
  "ninety",
];

const HUNDRED: &'static str = "hundred";

const THOUSANDS: [&'static str; 6] = [
  "thousand",
  "million",
  "billion",
  "trillion",
  "quadrillion",
  "quintillion",
  // TODO: Overflow in current algorithm.
  //  We'll need to use a u128 to go higher.
  //  But that seems like overkill.
  //"sextillion",
  //"septillion",
  //"octillion",
  //"nonillion",
];

// TODO: If I spend more time with the algorithm, this won't be necessary.
/// Library errors
#[derive(Debug,Clone)]
pub enum NumericsError {
  /// An error was encountered during conversion
  ConversionError,
}

/// *Numerics* can be configured to convert integer primitives into their respective english
/// word serializations.
pub struct Numerics {
  custom_negative_word: Option<String>,
}

/// *NumericsBuilder* lets you configure a *Numerics* instance.
pub struct NumericsBuilder {
  custom_negative_word: Option<String>,
}

impl Numerics {
  /// Configure a Numerics instance.
  pub fn builder() -> NumericsBuilder {
    NumericsBuilder{
      custom_negative_word: None,
    }
  }

  /// Return a default-configured instance.
  pub fn default() -> Self {
    Self::builder().build()
  }

  /// Convert a number into string.
  /// ```rust
  /// use numerics::Numerics;
  /// let converter = Numerics::default();
  ///
  /// assert_eq!(converter.convert_number(123).unwrap(),
  ///   vec!["one".to_string(), "hundred".to_string(), "twenty".to_string(), "three".to_string()]);
  /// ```
  pub fn convert_number<T>(&self, number: T) -> Result<Vec<String>, NumericsError>
    where T: Integer + PrimInt + SignedAndUnsigned + AsPrimitive<u64>
  {
    let mut words = Vec::new();

    if number.is_negative() {
      let negative_word = self.custom_negative_word
          .as_ref()
          .map(|word| word.clone())
          .unwrap_or(NEGATIVE.into());
      words.push(negative_word);
    }

    let unsigned_integer: u64 = match number.abs() {
      Some(n) => n.as_(),
      None => T::max_value().as_().saturating_add(1),
    };
    //let unsigned_integer: u64 = number.abs().unwrap().as_();

    let success = if unsigned_integer < 100 {
      self.convert_nn(unsigned_integer, &mut words)
    } else if unsigned_integer < 1000 {
      self.convert_nnn(unsigned_integer, &mut words)
    } else {
      self.convert_large(unsigned_integer, &mut words)
    };

    if !success {
      Err(NumericsError::ConversionError)
    } else {
      Ok(words)
    }
  }

  // TODO: This code is unchanged since 2016 when I was hastily writing a TTS engine.
  //  The algorithm may have been adapted from StackOverflow, but if so, it wasn't cited.
  //  This could be better idiomatic Rust.
  fn convert_nn(&self, number: u64, words: &mut Vec<String>) -> bool {
    if number < 20 {
      let word = BASE_NUMBERS[number as usize].to_string();
      words.push(word);
      return true;
    }

    for (i, word) in TENS.iter().enumerate() {
      let dval = 10 * i + 20;
      if dval + 10 > number as usize {
        if (number as usize % 10) != 0 {
          let first = word.to_string();
          let second = BASE_NUMBERS[(number % 10) as usize].to_string();

          words.push(first);
          words.push(second);
          return true;
        }
        words.push(word.to_string());
        return true;
      }
    }

    false // Should not be reached.
  }

  fn convert_nnn(&self, number: u64, words: &mut Vec<String>) -> bool {
    let rem = number / 100;
    if rem > 0 {
      words.push(BASE_NUMBERS[rem as usize].to_string());
      words.push(HUNDRED.to_string());
    }

    let md = number % 100;
    if md > 0 {
      if !self.convert_nn(md, words) {
        return false;
      }
    }

    true
  }

  fn convert_large(&self, number: u64, words: &mut Vec<String>) -> bool {
    if number < 1000 {
      if !self.convert_nnn(number, words) {
        return false;
      }
      return true;
    }

    // Iterate backwards, largest magnitudes first.
    for (i, unit) in THOUSANDS.iter().rev().enumerate() {
      let i = THOUSANDS.len() - i; // shadow
      let mag = 1000u64.pow(i as u32);

      if number < mag {
        continue;
      }

      let quo = number / mag;
      let rem = number - (quo * mag);

      if !self.convert_nnn(quo, words) {
        return false;
      }

      words.push(unit.to_string());

      if rem > 0 {
        if !self.convert_large(rem, words) {
          return false;
        }
      }

      return true;
    }

    false // Should not be reached.
  }
}

impl NumericsBuilder {

  /// Set a custom word to use to denote negative numbers.
  /// By default 'negative' is used, but you might want to use "minus" or some other word.
  /// You can unset your override by supplying 'None'.
  pub fn set_custom_negative_word(mut self, word: Option<&str>) -> NumericsBuilder {
    self.custom_negative_word = word.map(|s| s.to_string());
    self
  }

  /// Creates the Numerics instance, consuming the NumericsBuilder.
  pub fn build(self) -> Numerics {
    Numerics {
      custom_negative_word: self.custom_negative_word,
    }
  }
}

/// Signed number operations implemented for both signed and unsigned numbers.
pub trait SignedAndUnsigned : Sized {
  /// Minimum value for the type.
  const MINIMUM: Self;

  /// The absolute value of a number.
  /// If the number is signed and equal to ::MIN, this operation would normally panic at overflow in
  /// debug or return ::MIN in release. This is undesired behavior, so we return None instead.
  fn abs(&self) -> Option<Self>;

  /// Reports whether the number is negative.
  fn is_negative(&self) -> bool;
}

// NB: Code adapted from the 'num' crate.
// We needed to unify a few features of Signed and Unsigned numbers with a single trait.
macro_rules! signed_for_unsigned_impl {
  ($($t:ty)*) => ($(
    impl SignedAndUnsigned for $t {
      const MINIMUM : Self = <$t>::min_value();

      #[inline]
      fn abs(&self) -> Option<$t> {
        Some(*self)
      }

      #[inline]
      fn is_negative(&self) -> bool { false }
    }
  )*)
}

// TODO: Implement for u128
signed_for_unsigned_impl!(usize u8 u16 u32 u64);

// NB: Code adapted from the 'num' crate.
// We needed to unify a few features of Signed and Unsigned numbers with a single trait.
macro_rules! signed_impl {
  ($($t:ty)*) => ($(
    impl SignedAndUnsigned for $t {
      const MINIMUM : Self = <$t>::min_value();

      #[inline]
      fn abs(&self) -> Option<$t> {
        if self.is_negative() {
          if self == &Self::MINIMUM {
            return None;
          }
          Some(-*self)
        } else {
          Some(*self)
        }
      }

      #[inline]
      fn is_negative(&self) -> bool { *self < 0 }
    }
  )*)
}

// TODO: Implement for i128
signed_impl!(isize i8 i16 i32 i64);

// TODO: These tests are kind of gross to look at.
#[cfg(test)]
mod tests {
  use crate::Numerics;

  #[test]
  fn generics_for_all_integer_types_work() {
    let converter = Numerics::builder().build();

    // Test that the generics traits from the 'num' crate do what we want.
    assert_eq!(w("eight"), converter.convert_number(8u8).ok());
    assert_eq!(w("negative eight"), converter.convert_number(-8i8).ok());
    assert_eq!(w("sixteen"), converter.convert_number(16u16).ok());
    assert_eq!(w("negative sixteen"), converter.convert_number(-16i16).ok());
    assert_eq!(w("thirty two"), converter.convert_number(32u32).ok());
    assert_eq!(w("negative thirty two"), converter.convert_number(-32i32).ok());
    assert_eq!(w("sixty four"), converter.convert_number(64u64).ok());
    assert_eq!(w("negative sixty four"), converter.convert_number(-64i64).ok());
  }

  #[test]
  fn positive_integers_ones() {
    assert_eq!(w("zero"), number_to_words(0));
    assert_eq!(w("one"), number_to_words(1));
    assert_eq!(w("two"), number_to_words(2));
    assert_eq!(w("three"), number_to_words(3));
    assert_eq!(w("four"), number_to_words(4));
    assert_eq!(w("five"), number_to_words(5));
    assert_eq!(w("six"), number_to_words(6));
    assert_eq!(w("seven"), number_to_words(7));
    assert_eq!(w("eight"), number_to_words(8));
    assert_eq!(w("nine"), number_to_words(9));
  }

  #[test]
  fn negative_integers_ones() {
    assert_eq!(w("negative one"), number_to_words(-1));
    assert_eq!(w("negative two"), number_to_words(-2));
    assert_eq!(w("negative three"), number_to_words(-3));
    assert_eq!(w("negative four"), number_to_words(-4));
    assert_eq!(w("negative five"), number_to_words(-5));
    assert_eq!(w("negative six"), number_to_words(-6));
    assert_eq!(w("negative seven"), number_to_words(-7));
    assert_eq!(w("negative eight"), number_to_words(-8));
    assert_eq!(w("negative nine"), number_to_words(-9));
  }

  #[test]
  fn positive_integers_ten_thru_teens() {
    assert_eq!(w("ten"), number_to_words(10));
    assert_eq!(w("eleven"), number_to_words(11));
    assert_eq!(w("twelve"), number_to_words(12));
    assert_eq!(w("thirteen"), number_to_words(13));
    assert_eq!(w("fourteen"), number_to_words(14));
    assert_eq!(w("fifteen"), number_to_words(15));
    assert_eq!(w("sixteen"), number_to_words(16));
    assert_eq!(w("seventeen"), number_to_words(17));
    assert_eq!(w("eighteen"), number_to_words(18));
    assert_eq!(w("nineteen"), number_to_words(19));
  }

  #[test]
  fn positive_integers_tens() {
    assert_eq!(w("twenty"), number_to_words(20));
    assert_eq!(w("thirty"), number_to_words(30));
    assert_eq!(w("forty"), number_to_words(40));
    assert_eq!(w("fifty"), number_to_words(50));
    assert_eq!(w("sixty"), number_to_words(60));
    assert_eq!(w("seventy"), number_to_words(70));
    assert_eq!(w("eighty"), number_to_words(80));
    assert_eq!(w("ninety"), number_to_words(90));
  }

  #[test]
  fn positive_integers_hundreds() {
    assert_eq!(w("one hundred"), number_to_words(100));
    assert_eq!(w("two hundred"), number_to_words(200));
    assert_eq!(w("three hundred"), number_to_words(300));
    assert_eq!(w("four hundred"), number_to_words(400));
    assert_eq!(w("five hundred"), number_to_words(500));
    assert_eq!(w("six hundred"), number_to_words(600));
    assert_eq!(w("seven hundred"), number_to_words(700));
    assert_eq!(w("eight hundred"), number_to_words(800));
    assert_eq!(w("nine hundred"), number_to_words(900));
  }

  #[test]
  fn positive_integers_magnitudes() {
    assert_eq!(w("one thousand"), number_to_words(1_000));
    assert_eq!(w("one million"), number_to_words(1_000_000));
    assert_eq!(w("one billion"), number_to_words(1_000_000_000));
    assert_eq!(w("one trillion"), number_to_words(1_000_000_000_000));
  }

  #[test]
  fn unsigned_integer_bounds() {
    // This is a check against overflow
    let converter = Numerics::builder().build();
    // u8
    assert_eq!(w("zero"), converter.convert_number(u8::min_value()).ok());
    assert_eq!(w("two hundred fifty five"), converter.convert_number(u8::max_value()).ok());
    // u16
    assert_eq!(w("zero"), converter.convert_number(u16::min_value()).ok());
    assert_eq!(w("sixty five thousand five hundred thirty five"), converter.convert_number(u16::max_value()).ok());
    // u32
    assert_eq!(w("zero"), converter.convert_number(u32::min_value()).ok());
    assert_eq!(w("four billion two hundred ninety four million nine hundred sixty seven thousand two hundred ninety five"), converter.convert_number(u32::max_value()).ok());
    // u64
    assert_eq!(w("zero"), converter.convert_number(u64::min_value()).ok());
    assert_eq!(w(r#"eighteen quintillion four hundred forty six quadrillion seven hundred
                      forty four trillion seventy three billion seven hundred nine million five
                      hundred fifty one thousand six hundred fifteen"#), converter.convert_number(u64::max_value()).ok());
  }

  #[test]
  fn signed_integer_bounds() {
    // This is a check against overflow
    let converter = Numerics::builder().build();
    // i8
    assert_eq!(w("one hundred twenty seven"), converter.convert_number(i8::max_value()).ok());
    assert_eq!(w("negative one hundred twenty eight"), converter.convert_number(i8::min_value()).ok());
    // i16
    assert_eq!(w("thirty two thousand seven hundred sixty seven"), converter.convert_number(i16::max_value()).ok());
    assert_eq!(w("negative thirty two thousand seven hundred sixty eight"), converter.convert_number(i16::min_value()).ok());
    // i32
    assert_eq!(w(r#"two billion one hundred forty seven million four hundred eighty three
                      thousand six hundred forty seven"#), converter.convert_number(i32::max_value()).ok());
    assert_eq!(w(r#"negative two billion one hundred forty seven million four hundred eighty
                      three thousand six hundred forty eight"#), converter.convert_number(i32::min_value()).ok());
    // i64
    assert_eq!(w(r#"nine quintillion two hundred twenty three quadrillion three hundred
                        seventy two trillion thirty six billion eight hundred fifty four million
                        seven hundred seventy five thousand eight hundred seven"#), converter.convert_number(i64::max_value()).ok());
    assert_eq!(w(r#"negative nine quintillion two hundred twenty three quadrillion three
                        hundred seventy two trillion thirty six billion eight hundred fifty four
                        million seven hundred seventy five thousand eight hundred eight"#), converter.convert_number(i64::min_value()).ok());
  }

  #[test]
  fn positive_integers() {
    // Tens + Ones
    assert_eq!(w("twenty one"), number_to_words(21));
    assert_eq!(w("thirty five"), number_to_words(35));
    assert_eq!(w("forty four"), number_to_words(44));
    assert_eq!(w("fifty five"), number_to_words(55));
    assert_eq!(w("sixty six"), number_to_words(66));

    // Large with small prefix
    assert_eq!(w("nine thousand"), number_to_words(9_000));
    assert_eq!(w("ten million"), number_to_words(10_000_000));
    assert_eq!(w("sixty billion"), number_to_words(60_000_000_000));
    assert_eq!(w("four hundred forty four trillion"),
      number_to_words(444_000_000_000_000));

    // Large, multiple units
    assert_eq!(w("nine thousand one"), number_to_words(9_001));
    assert_eq!(w(r#"one hundred twenty three trillion
                    four hundred fifty six billion
                    seven hundred eighty nine million
                    one hundred twenty three thousand
                    four hundred fifty six"#),
      number_to_words(123_456_789_123_456));

    assert_eq!(w(r#"nine hundred ninety nine quadrillion
                    nine hundred ninety nine trillion
                    nine hundred ninety nine billion
                    nine hundred ninety nine million
                    nine hundred ninety nine thousand
                    nine hundred ninety nine"#),
      number_to_words(999_999_999_999_999_999));
    assert_eq!(w("one quintillion"), number_to_words(1_000_000_000_000_000_000));
  }

  #[test]
  fn negative_integers() {
    // Misc negative numbers.
    assert_eq!(w("negative one"), number_to_words(-1));
    assert_eq!(w("negative nine thousand one"), number_to_words(-9_001));
    assert_eq!(w("negative four hundred forty four trillion"),
      number_to_words(-444_000_000_000_000));

    assert_eq!(w(r#"negative one hundred twenty three trillion
                    four hundred fifty six billion
                    seven hundred eighty nine million
                    one hundred twenty three thousand
                    four hundred fifty six"#),
      number_to_words(-123_456_789_123_456));

    assert_eq!(w("zero"), number_to_words(-0));
    assert_eq!(w(r#"negative
                    nine hundred ninety nine quadrillion
                    nine hundred ninety nine trillion
                    nine hundred ninety nine billion
                    nine hundred ninety nine million
                    nine hundred ninety nine thousand
                    nine hundred ninety nine"#),
      number_to_words(-999_999_999_999_999_999));
    assert_eq!(w("negative one quintillion"), number_to_words(-1_000_000_000_000_000_000));
  }

  #[test]
  fn negative_word_config() {
    let negative_converter = Numerics::builder()
        .build();

    let minus_converter = Numerics::builder()
        .set_custom_negative_word(Some("minus"))
        .build();

    assert_eq!(w("negative one hundred"), negative_converter.convert_number(-100).ok());
    assert_eq!(w("minus one hundred"), minus_converter.convert_number(-100).ok());
  }

  // Test helper
  fn w(words: &str) -> Option<Vec<String>> {
    Some(words.split_whitespace().map(|s| s.to_string()).collect::<Vec<String>>())
  }

  // Test helper
  fn number_to_words(number: i64) -> Option<Vec<String>> {
    let converter = Numerics::builder().build();

    let s = converter.convert_number(number as i64)
        .ok()
        .unwrap();

    Some(s)
  }
}
