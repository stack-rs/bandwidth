#![cfg_attr(not(feature = "std"), no_std)]

use core::fmt::{self, Write};
use core::iter::Sum;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

const BPS_PER_GBPS: u32 = 1_000_000_000;
const BPS_PER_MBPS: u32 = 1_000_000;
const BPS_PER_KBPS: u32 = 1_000;
const MBPS_PER_GBPS: u64 = 1_000;
const KBPS_PER_GBPS: u64 = 1_000_000;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[derive(Default)]
struct BitPerSec(u32);

/// A `Bandwidth` type to represent a link's bandwidth(to describe how many bytes can be sent
/// on the link per second), typically used for network.
///
/// Each `Bandwidth` is composed of a whole number of gbps(gigabits per second) and a fractional part
/// represented in bps(bits per second). The fractional part should always in the range `[0, 1_000_000_000)`.
///
/// [`Bandwidth`]s implement many common traits, including [`Add`], [`Sub`], and other
/// [`ops`] traits. It implements [`Default`] by returning a zero-speed `Bandwidth`.
///
/// - gbps = gigabits per second
/// - mbps = megabits per second
/// - kbps = kilobits per second
/// - bps = bits per second
///
/// # Examples
///
/// ```
/// use bandwidth::Bandwidth;
///
/// let five_gbps = Bandwidth::new(5, 0);
/// let five_gbps_and_five_bps = five_gbps + Bandwidth::new(0, 5);
///
/// assert_eq!(five_gbps_and_five_bps.as_gbps(), 5);
/// assert_eq!(five_gbps_and_five_bps.subgbps_bps(), 5);
///
/// let ten_mbps = Bandwidth::from_mbps(10);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Bandwidth {
    gbps: u64,
    bps: BitPerSec, // Always 0 <= bps < BPS_PER_GBPS
}

impl Bandwidth {
    pub const MAX: Bandwidth = Bandwidth::new(u64::MAX, BPS_PER_GBPS - 1);
    pub const ZERO: Bandwidth = Bandwidth::new(0, 0);

    #[inline]
    pub const fn new(gbps: u64, bps: u32) -> Bandwidth {
        let gbps = match gbps.checked_add((bps / BPS_PER_GBPS) as u64) {
            Some(gbps) => gbps,
            None => panic!("overflow in Bandwidth::new"),
        };
        let bps = bps % BPS_PER_GBPS;
        Bandwidth {
            gbps,
            bps: BitPerSec(bps),
        }
    }

    /// Creates a new `Bandwidth` from the specified number of `gigabits per second`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_gbps(5);
    ///
    /// assert_eq!(5, Bandwidth.as_gbps());
    /// assert_eq!(0, Bandwidth.subgbps_bps());
    /// ```

    #[inline]

    pub const fn from_gbps(gbps: u64) -> Bandwidth {
        Bandwidth::new(gbps, 0)
    }

    /// Creates a new `Bandwidth` from the specified number of `megabits per second`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_mbps(2569);
    ///
    /// assert_eq!(2, Bandwidth.as_gbps());
    /// assert_eq!(569_000_000, Bandwidth.subgbps_bps());
    /// ```

    #[inline]

    pub const fn from_mbps(mbps: u64) -> Bandwidth {
        Bandwidth::new(
            mbps / MBPS_PER_GBPS,
            ((mbps % MBPS_PER_GBPS) as u32) * BPS_PER_MBPS,
        )
    }

    /// Creates a new `Bandwidth` from the specified number of `kilobits per second`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_kbps(1_000_002);
    ///
    /// assert_eq!(1, Bandwidth.as_gbps());
    /// assert_eq!(2000, Bandwidth.subgbps_bps());
    /// ```

    #[inline]

    pub const fn from_kbps(kbps: u64) -> Bandwidth {
        Bandwidth::new(
            kbps / KBPS_PER_GBPS,
            ((kbps % KBPS_PER_GBPS) as u32) * BPS_PER_KBPS,
        )
    }

    /// Creates a new `Bandwidth` from the specified number of `bits per second`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_bps(1_000_000_123);
    ///
    /// assert_eq!(1, Bandwidth.as_gbps());
    /// assert_eq!(123, Bandwidth.subgbps_bps());
    /// ```

    #[inline]

    pub const fn from_bps(bps: u64) -> Bandwidth {
        Bandwidth::new(
            bps / (BPS_PER_GBPS as u64),
            (bps % (BPS_PER_GBPS as u64)) as u32,
        )
    }

    /// Returns true if this `Bandwidth` has zero speed.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert!(Bandwidth::ZERO.is_zero());
    /// assert!(Bandwidth::new(0, 0).is_zero());
    /// assert!(Bandwidth::from_bps(0).is_zero());
    /// assert!(Bandwidth::from_gbps(0).is_zero());
    ///
    /// assert!(!Bandwidth::new(1, 1).is_zero());
    /// assert!(!Bandwidth::from_bps(1).is_zero());
    /// assert!(!Bandwidth::from_gbps(1).is_zero());
    /// ```

    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.gbps == 0 && self.bps.0 == 0
    }

    /// Returns the number of _whole_ gbps contained by this `Bandwidth`.
    ///
    /// The returned value does not include the fractional(bps) part of the
    /// Bandwidth, which can be obtained using [`subgbps_bps`].
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::new(5, 730023852);
    /// assert_eq!(Bandwidth.as_gbps(), 5);
    /// ```
    ///
    /// To determine the total number of gbps represented by the `Bandwidth`
    /// including the fractional part, use [`as_gbps_f64`] or [`as_gbps_f32`]
    ///
    /// [`as_gbps_f64`]: Bandwidth::as_gbps_f64
    /// [`as_gbps_f32`]: Bandwidth::as_gbps_f32
    /// [`subgbps_bps`]: Bandwidth::subgbps_bps

    #[inline]
    pub const fn as_gbps(&self) -> u64 {
        self.gbps
    }

    /// Returns the fractional part of this `Bandwidth`, in whole mbps.
    ///
    /// This method does **not** return the speed of the Bandwidth when
    /// represented by mbps. The returned number always represents a
    /// fractional portion of a gbps (i.e., it is less than one thousand).
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_mbps(5432);
    /// assert_eq!(Bandwidth.as_gbps(), 5);
    /// assert_eq!(Bandwidth.subgbps_mbps(), 432);
    /// ```

    #[inline]
    pub const fn subgbps_mbps(&self) -> u32 {
        self.bps.0 / BPS_PER_MBPS
    }

    /// Returns the fractional part of this `Bandwidth`, in whole kbps.
    ///
    /// This method does **not** return the speed of the Bandwidth when
    /// represented by kbps. The returned number always represents a
    /// fractional portion of a gbps (i.e., it is less than one million).
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_kbps(1_234_567);
    /// assert_eq!(Bandwidth.as_gbps(), 1);
    /// assert_eq!(Bandwidth.subgbps_kbps(), 234_567);
    /// ```

    #[inline]
    pub const fn subgbps_kbps(&self) -> u32 {
        self.bps.0 / BPS_PER_KBPS
    }

    /// Returns the fractional part of this `Bandwidth`, in bps.
    ///
    /// This method does **not** return the speed of the Bandwidth when
    /// represented by bps. The returned number always represents a
    /// fractional portion of a gbps (i.e., it is less than one billion).
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::from_mbps(5010);
    /// assert_eq!(Bandwidth.as_gbps(), 5);
    /// assert_eq!(Bandwidth.subgbps_bps(), 10_000_000);
    /// ```

    #[inline]
    pub const fn subgbps_bps(&self) -> u32 {
        self.bps.0
    }

    /// Returns the total number of whole mbps contained by this `Bandwidth`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::new(5, 730023852);
    /// assert_eq!(Bandwidth.as_mbps(), 5730);
    /// ```

    #[inline]
    pub const fn as_mbps(&self) -> u128 {
        self.gbps as u128 * MBPS_PER_GBPS as u128 + (self.bps.0 / BPS_PER_MBPS) as u128
    }

    /// Returns the total number of whole kbps contained by this `Bandwidth`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::new(5, 730023852);
    /// assert_eq!(Bandwidth.as_kbps(), 5730023);
    /// ```

    #[inline]
    pub const fn as_kbps(&self) -> u128 {
        self.gbps as u128 * KBPS_PER_GBPS as u128 + (self.bps.0 / BPS_PER_KBPS) as u128
    }

    /// Returns the total number of bps contained by this `Bandwidth`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let Bandwidth = Bandwidth::new(5, 730023852);
    /// assert_eq!(Bandwidth.as_bps(), 5730023852);
    /// ```

    #[inline]
    pub const fn as_bps(&self) -> u128 {
        self.gbps as u128 * BPS_PER_GBPS as u128 + self.bps.0 as u128
    }

    /// Checked `Bandwidth` addition. Computes `self + other`, returning [`None`]
    /// if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(0, 0).checked_add(Bandwidth::new(0, 1)), Some(Bandwidth::new(0, 1)));
    /// assert_eq!(Bandwidth::new(1, 0).checked_add(Bandwidth::new(u64::MAX, 0)), None);
    /// ```
    #[inline]
    pub const fn checked_add(self, rhs: Bandwidth) -> Option<Bandwidth> {
        if let Some(mut gbps) = self.gbps.checked_add(rhs.gbps) {
            let mut bps = self.bps.0 + rhs.bps.0;
            if bps >= BPS_PER_GBPS {
                bps -= BPS_PER_GBPS;
                if let Some(new_gbps) = gbps.checked_add(1) {
                    gbps = new_gbps;
                } else {
                    return None;
                }
            }
            debug_assert!(bps < BPS_PER_GBPS);
            Some(Bandwidth::new(gbps, bps))
        } else {
            None
        }
    }

    /// Saturating `Bandwidth` addition. Computes `self + other`, returning [`Bandwidth::MAX`]
    /// if overflow occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(0, 0).saturating_add(Bandwidth::new(0, 1)), Bandwidth::new(0, 1));
    /// assert_eq!(Bandwidth::new(1, 0).saturating_add(Bandwidth::new(u64::MAX, 0)), Bandwidth::MAX);
    /// ```
    #[inline]
    pub const fn saturating_add(self, rhs: Bandwidth) -> Bandwidth {
        match self.checked_add(rhs) {
            Some(res) => res,
            None => Bandwidth::MAX,
        }
    }

    /// Checked `Bandwidth` subtraction. Computes `self - other`, returning [`None`]
    /// if the result would be negative or if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(0, 1).checked_sub(Bandwidth::new(0, 0)), Some(Bandwidth::new(0, 1)));
    /// assert_eq!(Bandwidth::new(0, 0).checked_sub(Bandwidth::new(0, 1)), None);
    /// ```
    #[inline]
    pub const fn checked_sub(self, rhs: Bandwidth) -> Option<Bandwidth> {
        if let Some(mut gbps) = self.gbps.checked_sub(rhs.gbps) {
            let bps = if self.bps.0 >= rhs.bps.0 {
                self.bps.0 - rhs.bps.0
            } else if let Some(sub_gbps) = gbps.checked_sub(1) {
                gbps = sub_gbps;
                self.bps.0 + BPS_PER_GBPS - rhs.bps.0
            } else {
                return None;
            };
            debug_assert!(bps < BPS_PER_GBPS);
            Some(Bandwidth::new(gbps, bps))
        } else {
            None
        }
    }

    /// Saturating `Bandwidth` subtraction. Computes `self - other`, returning [`Bandwidth::ZERO`]
    /// if the result would be negative or if overflow occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(0, 1).saturating_sub(Bandwidth::new(0, 0)), Bandwidth::new(0, 1));
    /// assert_eq!(Bandwidth::new(0, 0).saturating_sub(Bandwidth::new(0, 1)), Bandwidth::ZERO);
    /// ```
    #[inline]
    pub const fn saturating_sub(self, rhs: Bandwidth) -> Bandwidth {
        match self.checked_sub(rhs) {
            Some(res) => res,
            None => Bandwidth::ZERO,
        }
    }

    /// Checked `Bandwidth` multiplication. Computes `self * other`, returning
    /// [`None`] if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(0, 500_000_001).checked_mul(2), Some(Bandwidth::new(1, 2)));
    /// assert_eq!(Bandwidth::new(u64::MAX - 1, 0).checked_mul(2), None);
    /// ```
    #[inline]
    pub const fn checked_mul(self, rhs: u32) -> Option<Bandwidth> {
        // Multiply bps as u64, because it cannot overflow that way.
        let total_bps = self.bps.0 as u64 * rhs as u64;
        let extra_gbps = total_bps / (BPS_PER_GBPS as u64);
        let bps = (total_bps % (BPS_PER_GBPS as u64)) as u32;
        if let Some(s) = self.gbps.checked_mul(rhs as u64) {
            if let Some(gbps) = s.checked_add(extra_gbps) {
                debug_assert!(bps < BPS_PER_GBPS);
                return Some(Bandwidth::new(gbps, bps));
            }
        }
        None
    }

    /// Saturating `Bandwidth` multiplication. Computes `self * other`, returning
    /// [`Bandwidth::MAX`] if overflow occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(0, 500_000_001).saturating_mul(2), Bandwidth::new(1, 2));
    /// assert_eq!(Bandwidth::new(u64::MAX - 1, 0).saturating_mul(2), Bandwidth::MAX);
    /// ```
    #[inline]
    pub const fn saturating_mul(self, rhs: u32) -> Bandwidth {
        match self.checked_mul(rhs) {
            Some(res) => res,
            None => Bandwidth::MAX,
        }
    }

    /// Checked `Bandwidth` division. Computes `self / other`, returning [`None`]
    /// if `other == 0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// assert_eq!(Bandwidth::new(2, 0).checked_div(2), Some(Bandwidth::new(1, 0)));
    /// assert_eq!(Bandwidth::new(1, 0).checked_div(2), Some(Bandwidth::new(0, 500_000_000)));
    /// assert_eq!(Bandwidth::new(2, 0).checked_div(0), None);
    /// ```
    #[inline]
    pub const fn checked_div(self, rhs: u32) -> Option<Bandwidth> {
        if rhs != 0 {
            let gbps = self.gbps / (rhs as u64);
            let carry = self.gbps - gbps * (rhs as u64);
            let extra_bps = carry * (BPS_PER_GBPS as u64) / (rhs as u64);
            let bps = self.bps.0 / rhs + (extra_bps as u32);
            debug_assert!(bps < BPS_PER_GBPS);
            Some(Bandwidth::new(gbps, bps))
        } else {
            None
        }
    }

    /// Returns the number of gbps contained by this `Bandwidth` as `f64`.
    ///
    /// The returned value does include the fractional (bps) part of the Bandwidth.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw = Bandwidth::new(2, 700_000_000);
    /// assert_eq!(bw.as_gbps_f64(), 2.7);
    /// ```
    #[inline]
    pub fn as_gbps_f64(&self) -> f64 {
        (self.gbps as f64) + (self.bps.0 as f64) / (BPS_PER_GBPS as f64)
    }

    /// Returns the number of gbps contained by this `Bandwidth` as `f32`.
    ///
    /// The returned value does include the fractional (bps) part of the Bandwidth.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw = Bandwidth::new(2, 700_000_000);
    /// assert_eq!(bw.as_gbps_f32(), 2.7);
    /// ```
    #[inline]
    pub fn as_gbps_f32(&self) -> f32 {
        (self.gbps as f32) + (self.bps.0 as f32) / (BPS_PER_GBPS as f32)
    }

    /// Creates a new `Bandwidth` from the specified number of gbps represented
    /// as `f64`.
    ///
    /// # Panics
    /// This constructor will panic if `gbps` is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let res = Bandwidth::from_gbps_f64(0.0);
    /// assert_eq!(res, Bandwidth::new(0, 0));
    /// let res = Bandwidth::from_gbps_f64(1e-20);
    /// assert_eq!(res, Bandwidth::new(0, 0));
    /// let res = Bandwidth::from_gbps_f64(4.2e-7);
    /// assert_eq!(res, Bandwidth::new(0, 420));
    /// let res = Bandwidth::from_gbps_f64(2.7);
    /// assert_eq!(res, Bandwidth::new(2, 700_000_000));
    /// let res = Bandwidth::from_gbps_f64(3e10);
    /// assert_eq!(res, Bandwidth::new(30_000_000_000, 0));
    /// // subnormal float
    /// let res = Bandwidth::from_gbps_f64(f64::from_bits(1));
    /// assert_eq!(res, Bandwidth::new(0, 0));
    /// // conversion uses rounding
    /// let res = Bandwidth::from_gbps_f64(0.999e-9);
    /// assert_eq!(res, Bandwidth::new(0, 1));
    /// ```
    #[inline]
    pub fn from_gbps_f64(gbps: f64) -> Bandwidth {
        match Bandwidth::try_from_gbps_f64(gbps) {
            Ok(v) => v,
            Err(e) => panic!("{}", e.description()),
        }
    }

    /// Creates a new `Bandwidth` from the specified number of gbps represented
    /// as `f32`.
    ///
    /// # Panics
    /// This constructor will panic if `gbps` is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let res = Bandwidth::from_gbps_f32(0.0);
    /// assert_eq!(res, Bandwidth::new(0, 0));
    /// let res = Bandwidth::from_gbps_f32(1e-20);
    /// assert_eq!(res, Bandwidth::new(0, 0));
    /// let res = Bandwidth::from_gbps_f32(4.2e-7);
    /// assert_eq!(res, Bandwidth::new(0, 420));
    /// let res = Bandwidth::from_gbps_f32(2.7);
    /// assert_eq!(res, Bandwidth::new(2, 700_000_048));
    /// let res = Bandwidth::from_gbps_f32(3e10);
    /// assert_eq!(res, Bandwidth::new(30_000_001_024, 0));
    /// // subnormal float
    /// let res = Bandwidth::from_gbps_f32(f32::from_bits(1));
    /// assert_eq!(res, Bandwidth::new(0, 0));
    /// // conversion uses rounding
    /// let res = Bandwidth::from_gbps_f32(0.999e-9);
    /// assert_eq!(res, Bandwidth::new(0, 1));
    /// ```
    #[inline]
    pub fn from_gbps_f32(gbps: f32) -> Bandwidth {
        match Bandwidth::try_from_gbps_f32(gbps) {
            Ok(v) => v,
            Err(e) => panic!("{}", e.description()),
        }
    }

    /// Multiplies `Bandwidth` by `f64`.
    ///
    /// # Panics
    /// This method will panic if result is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw = Bandwidth::new(2, 700_000_000);
    /// assert_eq!(bw.mul_f64(3.14), Bandwidth::new(8, 478_000_000));
    /// assert_eq!(bw.mul_f64(3.14e5), Bandwidth::new(847_800, 0));
    /// ```
    #[inline]
    pub fn mul_f64(self, rhs: f64) -> Bandwidth {
        Bandwidth::from_gbps_f64(rhs * self.as_gbps_f64())
    }

    /// Multiplies `Bandwidth` by `f32`.
    ///
    /// # Panics
    /// This method will panic if result is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw = Bandwidth::new(2, 700_000_000);
    /// assert_eq!(bw.mul_f32(3.14), Bandwidth::new(8, 478_000_641));
    /// assert_eq!(bw.mul_f32(3.14e5), Bandwidth::new(847800, 0));
    /// ```
    #[inline]
    pub fn mul_f32(self, rhs: f32) -> Bandwidth {
        Bandwidth::from_gbps_f32(rhs * self.as_gbps_f32())
    }

    /// Divide `Bandwidth` by `f64`.
    ///
    /// # Panics
    /// This method will panic if result is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw = Bandwidth::new(2, 700_000_000);
    /// assert_eq!(bw.div_f64(3.14), Bandwidth::new(0, 859_872_611));
    /// assert_eq!(bw.div_f64(3.14e5), Bandwidth::new(0, 8_599));
    /// ```
    #[inline]
    pub fn div_f64(self, rhs: f64) -> Bandwidth {
        Bandwidth::from_gbps_f64(self.as_gbps_f64() / rhs)
    }

    /// Divide `Bandwidth` by `f32`.
    ///
    /// # Panics
    /// This method will panic if result is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw = Bandwidth::new(2, 700_000_000);
    /// // note that due to rounding errors result is slightly
    /// // different from 0.859_872_611
    /// assert_eq!(bw.div_f32(3.14), Bandwidth::new(0, 859_872_580));
    /// assert_eq!(bw.div_f32(3.14e5), Bandwidth::new(0, 8_599));
    /// ```
    #[inline]
    pub fn div_f32(self, rhs: f32) -> Bandwidth {
        Bandwidth::from_gbps_f32(self.as_gbps_f32() / rhs)
    }

    /// Divide `Bandwidth` by `Bandwidth` and return `f64`.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw1 = Bandwidth::new(2, 700_000_000);
    /// let bw2 = Bandwidth::new(5, 400_000_000);
    /// assert_eq!(bw1.div_bandwidth_f64(bw2), 0.5);
    /// ```
    #[inline]
    pub fn div_bandwidth_f64(self, rhs: Bandwidth) -> f64 {
        self.as_gbps_f64() / rhs.as_gbps_f64()
    }

    /// Divide `Bandwidth` by `Bandwidth` and return `f32`.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let bw1 = Bandwidth::new(2, 700_000_000);
    /// let bw2 = Bandwidth::new(5, 400_000_000);
    /// assert_eq!(bw1.div_bandwidth_f32(bw2), 0.5);
    /// ```
    #[inline]
    pub fn div_bandwidth_f32(self, rhs: Bandwidth) -> f32 {
        self.as_gbps_f32() / rhs.as_gbps_f32()
    }
}

impl Add for Bandwidth {
    type Output = Bandwidth;

    fn add(self, rhs: Bandwidth) -> Bandwidth {
        self.checked_add(rhs)
            .expect("overflow when adding Bandwidths")
    }
}

impl AddAssign for Bandwidth {
    fn add_assign(&mut self, rhs: Bandwidth) {
        *self = *self + rhs;
    }
}

impl Sub for Bandwidth {
    type Output = Bandwidth;

    fn sub(self, rhs: Bandwidth) -> Bandwidth {
        self.checked_sub(rhs)
            .expect("overflow when subtracting Bandwidths")
    }
}

impl SubAssign for Bandwidth {
    fn sub_assign(&mut self, rhs: Bandwidth) {
        *self = *self - rhs;
    }
}

impl Mul<u32> for Bandwidth {
    type Output = Bandwidth;

    fn mul(self, rhs: u32) -> Bandwidth {
        self.checked_mul(rhs)
            .expect("overflow when multiplying Bandwidth by scalar")
    }
}

impl Mul<Bandwidth> for u32 {
    type Output = Bandwidth;

    fn mul(self, rhs: Bandwidth) -> Bandwidth {
        rhs * self
    }
}

impl MulAssign<u32> for Bandwidth {
    fn mul_assign(&mut self, rhs: u32) {
        *self = *self * rhs;
    }
}

impl Div<u32> for Bandwidth {
    type Output = Bandwidth;

    fn div(self, rhs: u32) -> Bandwidth {
        self.checked_div(rhs)
            .expect("divide by zero error when dividing Bandwidth by scalar")
    }
}

impl DivAssign<u32> for Bandwidth {
    fn div_assign(&mut self, rhs: u32) {
        *self = *self / rhs;
    }
}

macro_rules! sum_Bandwidths {
    ($iter:expr) => {{
        let mut total_gbps: u64 = 0;
        let mut total_bps: u64 = 0;

        for entry in $iter {
            total_gbps = total_gbps
                .checked_add(entry.gbps)
                .expect("overflow in iter::sum over bandwidths");
            total_bps = match total_bps.checked_add(entry.bps.0 as u64) {
                Some(n) => n,
                None => {
                    total_gbps = total_gbps
                        .checked_add(total_bps / BPS_PER_GBPS as u64)
                        .expect("overflow in iter::sum over bandwidths");
                    (total_bps % BPS_PER_GBPS as u64) + entry.bps.0 as u64
                }
            };
        }
        total_gbps = total_gbps
            .checked_add(total_bps / BPS_PER_GBPS as u64)
            .expect("overflow in iter::sum over bandwidths");
        total_bps %= BPS_PER_GBPS as u64;
        Bandwidth::new(total_gbps, total_bps as u32)
    }};
}

impl Sum for Bandwidth {
    fn sum<I: Iterator<Item = Bandwidth>>(iter: I) -> Bandwidth {
        sum_Bandwidths!(iter)
    }
}

impl<'a> Sum<&'a Bandwidth> for Bandwidth {
    fn sum<I: Iterator<Item = &'a Bandwidth>>(iter: I) -> Bandwidth {
        sum_Bandwidths!(iter)
    }
}

/// An error which can be returned when converting a floating-point value of gbps
/// into a [`Bandwidth`].
///
/// This error is used as the error type for [`Bandwidth::try_from_gbps_f32`] and
/// [`Bandwidth::try_from_gbps_f64`].
///
/// # Example
///
/// ```
/// use bandwidth::Bandwidth;
///
/// if let Err(e) = Bandwidth::try_from_gbps_f32(-1.0) {
///     println!("Failed conversion to Bandwidth: {e}");
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TryFromFloatGbpsError {
    kind: TryFromFloatGbpsErrorKind,
}

impl TryFromFloatGbpsError {
    const fn description(&self) -> &'static str {
        match self.kind {
            TryFromFloatGbpsErrorKind::Negative => {
                "can not convert float gbps to Bandwidth: value is negative"
            }
            TryFromFloatGbpsErrorKind::OverflowOrNan => {
                "can not convert float gbps to Bandwidth: value is either too big or NaN"
            }
        }
    }
}

impl fmt::Display for TryFromFloatGbpsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.description().fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TryFromFloatGbpsErrorKind {
    // Value is negative.
    Negative,
    // Value is either too big to be represented as `Bandwidth` or `NaN`.
    OverflowOrNan,
}

macro_rules! try_from_gbps {
    (
        gbps = $gbps: expr,
        mantissa_bits = $mant_bits: literal,
        exponent_bits = $exp_bits: literal,
        offset = $offset: literal,
        bits_ty = $bits_ty:ty,
        double_ty = $double_ty:ty,
    ) => {{
        const MIN_EXP: i16 = 1 - (1i16 << $exp_bits) / 2;
        const MANT_MASK: $bits_ty = (1 << $mant_bits) - 1;
        const EXP_MASK: $bits_ty = (1 << $exp_bits) - 1;

        if $gbps < 0.0 {
            return Err(TryFromFloatGbpsError {
                kind: TryFromFloatGbpsErrorKind::Negative,
            });
        }

        let bits = $gbps.to_bits();
        let mant = (bits & MANT_MASK) | (MANT_MASK + 1);
        let exp = ((bits >> $mant_bits) & EXP_MASK) as i16 + MIN_EXP;

        let (gbps, bps) = if exp < -31 {
            // the input represents less than 1ns and can not be rounded to it
            (0u64, 0u32)
        } else if exp < 0 {
            // the input is less than 1 second
            let t = <$double_ty>::from(mant) << ($offset + exp);
            let bps_offset = $mant_bits + $offset;
            let bps_tmp = u128::from(BPS_PER_GBPS) * u128::from(t);
            let bps = (bps_tmp >> bps_offset) as u32;

            let rem_mask = (1 << bps_offset) - 1;
            let rem_msb_mask = 1 << (bps_offset - 1);
            let rem = bps_tmp & rem_mask;
            let is_tie = rem == rem_msb_mask;
            let is_even = (bps & 1) == 0;
            let rem_msb = bps_tmp & rem_msb_mask == 0;
            let add_bps = !(rem_msb || (is_even && is_tie));

            let bps = bps + add_bps as u32;
            if ($mant_bits == 23) || (bps != BPS_PER_GBPS) {
                (0, bps)
            } else {
                (1, 0)
            }
        } else if exp < $mant_bits {
            let gbps = u64::from(mant >> ($mant_bits - exp));
            let t = <$double_ty>::from((mant << exp) & MANT_MASK);
            let bps_offset = $mant_bits;
            let bps_tmp = <$double_ty>::from(BPS_PER_GBPS) * t;
            let bps = (bps_tmp >> bps_offset) as u32;

            let rem_mask = (1 << bps_offset) - 1;
            let rem_msb_mask = 1 << (bps_offset - 1);
            let rem = bps_tmp & rem_mask;
            let is_tie = rem == rem_msb_mask;
            let is_even = (bps & 1) == 0;
            let rem_msb = bps_tmp & rem_msb_mask == 0;
            let add_bps = !(rem_msb || (is_even && is_tie));

            let bps = bps + add_bps as u32;
            if ($mant_bits == 23) || (bps != BPS_PER_GBPS) {
                (gbps, bps)
            } else {
                (gbps + 1, 0)
            }
        } else if exp < 64 {
            // the input has no fractional part
            let gbps = u64::from(mant) << (exp - $mant_bits);
            (gbps, 0)
        } else {
            return Err(TryFromFloatGbpsError {
                kind: TryFromFloatGbpsErrorKind::OverflowOrNan,
            });
        };

        Ok(Bandwidth::new(gbps, bps))
    }};
}

impl Bandwidth {
    /// The checked version of [`from_gbps_f32`].
    ///
    /// [`from_gbps_f32`]: Bandwidth::from_gbps_f32
    ///
    /// This constructor will return an `Err` if `gbps` is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let res = Bandwidth::try_from_gbps_f32(0.0);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 0)));
    /// let res = Bandwidth::try_from_gbps_f32(1e-20);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 0)));
    /// let res = Bandwidth::try_from_gbps_f32(4.2e-7);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 420)));
    /// let res = Bandwidth::try_from_gbps_f32(2.7);
    /// assert_eq!(res, Ok(Bandwidth::new(2, 700_000_048)));
    /// let res = Bandwidth::try_from_gbps_f32(3e10);
    /// assert_eq!(res, Ok(Bandwidth::new(30_000_001_024, 0)));
    /// // subnormal float:
    /// let res = Bandwidth::try_from_gbps_f32(f32::from_bits(1));
    /// assert_eq!(res, Ok(Bandwidth::new(0, 0)));
    ///
    /// let res = Bandwidth::try_from_gbps_f32(-5.0);
    /// assert!(res.is_err());
    /// let res = Bandwidth::try_from_gbps_f32(f32::NAN);
    /// assert!(res.is_err());
    /// let res = Bandwidth::try_from_gbps_f32(2e19);
    /// assert!(res.is_err());
    ///
    /// // the conversion uses rounding with tie resolution to even
    /// let res = Bandwidth::try_from_gbps_f32(0.999e-9);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 1)));
    ///
    /// // this float represents exactly 976562.5e-9
    /// let val = f32::from_bits(0x3A80_0000);
    /// let res = Bandwidth::try_from_gbps_f32(val);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 976_562)));
    ///
    /// // this float represents exactly 2929687.5e-9
    /// let val = f32::from_bits(0x3B40_0000);
    /// let res = Bandwidth::try_from_gbps_f32(val);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 2_929_688)));
    ///
    /// // this float represents exactly 1.000_976_562_5
    /// let val = f32::from_bits(0x3F802000);
    /// let res = Bandwidth::try_from_gbps_f32(val);
    /// assert_eq!(res, Ok(Bandwidth::new(1, 976_562)));
    ///
    /// // this float represents exactly 1.002_929_687_5
    /// let val = f32::from_bits(0x3F806000);
    /// let res = Bandwidth::try_from_gbps_f32(val);
    /// assert_eq!(res, Ok(Bandwidth::new(1, 2_929_688)));
    /// ```
    #[inline]
    pub fn try_from_gbps_f32(gbps: f32) -> Result<Bandwidth, TryFromFloatGbpsError> {
        try_from_gbps!(
            gbps = gbps,
            mantissa_bits = 23,
            exponent_bits = 8,
            offset = 41,
            bits_ty = u32,
            double_ty = u64,
        )
    }

    /// The checked version of [`from_gbps_f64`].
    ///
    /// [`from_gbps_f64`]: Bandwidth::from_gbps_f64
    ///
    /// This constructor will return an `Err` if `secs` is negative, overflows `Bandwidth` or not finite.
    ///
    /// # Examples
    /// ```
    /// use bandwidth::Bandwidth;
    ///
    /// let res = Bandwidth::try_from_gbps_f64(0.0);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 0)));
    /// let res = Bandwidth::try_from_gbps_f64(1e-20);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 0)));
    /// let res = Bandwidth::try_from_gbps_f64(4.2e-7);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 420)));
    /// let res = Bandwidth::try_from_gbps_f64(2.7);
    /// assert_eq!(res, Ok(Bandwidth::new(2, 700_000_000)));
    /// let res = Bandwidth::try_from_gbps_f64(3e10);
    /// assert_eq!(res, Ok(Bandwidth::new(30_000_000_000, 0)));
    /// // subnormal float
    /// let res = Bandwidth::try_from_gbps_f64(f64::from_bits(1));
    /// assert_eq!(res, Ok(Bandwidth::new(0, 0)));
    ///
    /// let res = Bandwidth::try_from_gbps_f64(-5.0);
    /// assert!(res.is_err());
    /// let res = Bandwidth::try_from_gbps_f64(f64::NAN);
    /// assert!(res.is_err());
    /// let res = Bandwidth::try_from_gbps_f64(2e19);
    /// assert!(res.is_err());
    ///
    /// // the conversion uses rounding with tie resolution to even
    /// let res = Bandwidth::try_from_gbps_f64(0.999e-9);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 1)));
    /// let res = Bandwidth::try_from_gbps_f64(0.999_999_999_499);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 999_999_999)));
    /// let res = Bandwidth::try_from_gbps_f64(0.999_999_999_501);
    /// assert_eq!(res, Ok(Bandwidth::new(1, 0)));
    /// let res = Bandwidth::try_from_gbps_f64(42.999_999_999_499);
    /// assert_eq!(res, Ok(Bandwidth::new(42, 999_999_999)));
    /// let res = Bandwidth::try_from_gbps_f64(42.999_999_999_501);
    /// assert_eq!(res, Ok(Bandwidth::new(43, 0)));
    ///
    /// // this float represents exactly 976562.5e-9
    /// let val = f64::from_bits(0x3F50_0000_0000_0000);
    /// let res = Bandwidth::try_from_gbps_f64(val);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 976_562)));
    ///
    /// // this float represents exactly 2929687.5e-9
    /// let val = f64::from_bits(0x3F68_0000_0000_0000);
    /// let res = Bandwidth::try_from_gbps_f64(val);
    /// assert_eq!(res, Ok(Bandwidth::new(0, 2_929_688)));
    ///
    /// // this float represents exactly 1.000_976_562_5
    /// let val = f64::from_bits(0x3FF0_0400_0000_0000);
    /// let res = Bandwidth::try_from_gbps_f64(val);
    /// assert_eq!(res, Ok(Bandwidth::new(1, 976_562)));
    ///
    /// // this float represents exactly 1.002_929_687_5
    /// let val = f64::from_bits(0x3_FF00_C000_0000_000);
    /// let res = Bandwidth::try_from_gbps_f64(val);
    /// assert_eq!(res, Ok(Bandwidth::new(1, 2_929_688)));
    /// ```
    #[inline]
    pub fn try_from_gbps_f64(gbps: f64) -> Result<Bandwidth, TryFromFloatGbpsError> {
        try_from_gbps!(
            gbps = gbps,
            mantissa_bits = 52,
            exponent_bits = 11,
            offset = 44,
            bits_ty = u64,
            double_ty = u128,
        )
    }
}

#[rustversion::before(1.67)]
impl fmt::Debug for Bandwidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Formats a floating point number in decimal notation.
        ///
        /// The number is given as the `integer_part` and a fractional part.
        /// The value of the fractional part is `fractional_part / divisor`. So
        /// `integer_part` = 3, `fractional_part` = 12 and `divisor` = 100
        /// represents the number `3.012`. Trailing zeros are omitted.
        ///
        /// `divisor` must not be above 100_000_000. It also should be a power
        /// of 10, everything else doesn't make sense. `fractional_part` has
        /// to be less than `10 * divisor`!
        ///
        /// This function is copied from older rust stable version since
        /// `checked_ilog10` is just stabled in 1.67
        fn fmt_decimal(
            f: &mut fmt::Formatter<'_>,
            mut integer_part: u64,
            mut fractional_part: u32,
            mut divisor: u32,
        ) -> fmt::Result {
            // Encode the fractional part into a temporary buffer. The buffer
            // only need to hold 9 elements, because `fractional_part` has to
            // be smaller than 10^9. The buffer is prefilled with '0' digits
            // to simplify the code below.
            let mut buf = [b'0'; 9];

            // The next digit is written at this position
            let mut pos = 0;

            // We keep writing digits into the buffer while there are non-zero
            // digits left and we haven't written enough digits yet.
            while fractional_part > 0 && pos < f.precision().unwrap_or(9) {
                // Write new digit into the buffer
                buf[pos] = b'0' + (fractional_part / divisor) as u8;

                fractional_part %= divisor;
                divisor /= 10;
                pos += 1;
            }

            // If a precision < 9 was specified, there may be some non-zero
            // digits left that weren't written into the buffer. In that case we
            // need to perform rounding to match the semantics of printing
            // normal floating point numbers. However, we only need to do work
            // when rounding up. This happens if the first digit of the
            // remaining ones is >= 5.
            if fractional_part > 0 && fractional_part >= divisor * 5 {
                // Round up the number contained in the buffer. We go through
                // the buffer backwards and keep track of the carry.
                let mut rev_pos = pos;
                let mut carry = true;
                while carry && rev_pos > 0 {
                    rev_pos -= 1;

                    // If the digit in the buffer is not '9', we just need to
                    // increment it and can stop then (since we don't have a
                    // carry anymore). Otherwise, we set it to '0' (overflow)
                    // and continue.
                    if buf[rev_pos] < b'9' {
                        buf[rev_pos] += 1;
                        carry = false;
                    } else {
                        buf[rev_pos] = b'0';
                    }
                }

                // If we still have the carry bit set, that means that we set
                // the whole buffer to '0's and need to increment the integer
                // part.
                if carry {
                    integer_part += 1;
                }
            }

            // Determine the end of the buffer: if precision is set, we just
            // use as many digits from the buffer (capped to 9). If it isn't
            // set, we only use all digits up to the last non-zero one.
            let end = f.precision().map(|p| core::cmp::min(p, 9)).unwrap_or(pos);

            // If we haven't emitted a single fractional digit and the precision
            // wasn't set to a non-zero value, we don't print the decimal point.
            if end == 0 {
                write!(f, "{}", integer_part)
            } else {
                // SAFETY: We are only writing ASCII digits into the buffer and it was
                // initialized with '0's, so it contains valid UTF8.
                let s = unsafe { core::str::from_utf8_unchecked(&buf[..end]) };

                // If the user request a precision > 9, we pad '0's at the end.
                let w = f.precision().unwrap_or(pos);
                write!(f, "{}.{:0<width$}", integer_part, s, width = w)
            }
        }

        // Print leading '+' sign if requested
        if f.sign_plus() {
            write!(f, "+")?;
        }

        if self.gbps > 0 {
            fmt_decimal(f, self.gbps, self.bps.0, BPS_PER_GBPS / 10)?;
            f.write_str("gbps")
        } else if self.bps.0 >= BPS_PER_MBPS {
            fmt_decimal(
                f,
                (self.bps.0 / BPS_PER_MBPS) as u64,
                self.bps.0 % BPS_PER_MBPS,
                BPS_PER_MBPS / 10,
            )?;
            f.write_str("mbps")
        } else if self.bps.0 >= BPS_PER_KBPS {
            fmt_decimal(
                f,
                (self.bps.0 / BPS_PER_KBPS) as u64,
                self.bps.0 % BPS_PER_KBPS,
                BPS_PER_KBPS / 10,
            )?;
            f.write_str("kbps")
        } else {
            fmt_decimal(f, self.bps.0 as u64, 0, 1)?;
            f.write_str("bps")
        }
    }
}

#[rustversion::since(1.67)]
impl fmt::Debug for Bandwidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Formats a floating point number in decimal notation.
        ///
        /// The number is given as the `integer_part` and a fractional part.
        /// The value of the fractional part is `fractional_part / divisor`. So
        /// `integer_part` = 3, `fractional_part` = 12 and `divisor` = 100
        /// represents the number `3.012`. Trailing zeros are omitted.
        ///
        /// `divisor` must not be above 100_000_000. It also should be a power
        /// of 10, everything else doesn't make sense. `fractional_part` has
        /// to be less than `10 * divisor`!
        ///
        /// A prefix and postfix may be added. The whole thing is padded
        /// to the formatter's `width`, if specified.
        fn fmt_decimal(
            f: &mut fmt::Formatter<'_>,
            integer_part: u64,
            mut fractional_part: u32,
            mut divisor: u32,
            prefix: &str,
            postfix: &str,
        ) -> fmt::Result {
            // Encode the fractional part into a temporary buffer. The buffer
            // only need to hold 9 elements, because `fractional_part` has to
            // be smaller than 10^9. The buffer is prefilled with '0' digits
            // to simplify the code below.
            let mut buf = [b'0'; 9];

            // The next digit is written at this position
            let mut pos = 0;

            // We keep writing digits into the buffer while there are non-zero
            // digits left and we haven't written enough digits yet.
            while fractional_part > 0 && pos < f.precision().unwrap_or(9) {
                // Write new digit into the buffer
                buf[pos] = b'0' + (fractional_part / divisor) as u8;

                fractional_part %= divisor;
                divisor /= 10;
                pos += 1;
            }

            // If a precision < 9 was specified, there may be some non-zero
            // digits left that weren't written into the buffer. In that case we
            // need to perform rounding to match the semantics of printing
            // normal floating point numbers. However, we only need to do work
            // when rounding up. This happens if the first digit of the
            // remaining ones is >= 5.
            let integer_part = if fractional_part > 0 && fractional_part >= divisor * 5 {
                // Round up the number contained in the buffer. We go through
                // the buffer backwards and keep track of the carry.
                let mut rev_pos = pos;
                let mut carry = true;
                while carry && rev_pos > 0 {
                    rev_pos -= 1;

                    // If the digit in the buffer is not '9', we just need to
                    // increment it and can stop then (since we don't have a
                    // carry anymore). Otherwise, we set it to '0' (overflow)
                    // and continue.
                    if buf[rev_pos] < b'9' {
                        buf[rev_pos] += 1;
                        carry = false;
                    } else {
                        buf[rev_pos] = b'0';
                    }
                }

                // If we still have the carry bit set, that means that we set
                // the whole buffer to '0's and need to increment the integer
                // part.
                if carry {
                    // If `integer_part == u64::MAX` and precision < 9, any
                    // carry of the overflow during rounding of the
                    // `fractional_part` into the `integer_part` will cause the
                    // `integer_part` itself to overflow. Avoid this by using an
                    // `Option<u64>`, with `None` representing `u64::MAX + 1`.
                    integer_part.checked_add(1)
                } else {
                    Some(integer_part)
                }
            } else {
                Some(integer_part)
            };

            // Determine the end of the buffer: if precision is set, we just
            // use as many digits from the buffer (capped to 9). If it isn't
            // set, we only use all digits up to the last non-zero one.
            let end = f.precision().map(|p| core::cmp::min(p, 9)).unwrap_or(pos);

            // This closure emits the formatted duration without emitting any
            // padding (padding is calculated below).
            let emit_without_padding = |f: &mut fmt::Formatter<'_>| {
                if let Some(integer_part) = integer_part {
                    write!(f, "{prefix}{integer_part}")?;
                } else {
                    // u64::MAX + 1 == 18446744073709551616
                    write!(f, "{prefix}18446744073709551616")?;
                }

                // Write the decimal point and the fractional part (if any).
                if end > 0 {
                    // SAFETY: We are only writing ASCII digits into the buffer and
                    // it was initialized with '0's, so it contains valid UTF8.
                    let s = unsafe { core::str::from_utf8_unchecked(&buf[..end]) };

                    // If the user request a precision > 9, we pad '0's at the end.
                    let w = f.precision().unwrap_or(pos);
                    write!(f, ".{s:0<w$}")?;
                }

                write!(f, "{postfix}")
            };

            match f.width() {
                None => {
                    // No `width` specified. There's no need to calculate the
                    // length of the output in this case, just emit it.
                    emit_without_padding(f)
                }
                Some(requested_w) => {
                    // A `width` was specified. Calculate the actual width of
                    // the output in order to calculate the required padding.
                    // It consists of 4 parts:
                    // 1. The prefix: is either "+" or "", so we can just use len().
                    // 2. The postfix: can be "µs" so we have to count UTF8 characters.
                    let mut actual_w = prefix.len() + postfix.chars().count();
                    // 3. The integer part:
                    if let Some(integer_part) = integer_part {
                        if let Some(log) = integer_part.checked_ilog10() {
                            // integer_part is > 0, so has length log10(x)+1
                            actual_w += 1 + log as usize;
                        } else {
                            // integer_part is 0, so has length 1.
                            actual_w += 1;
                        }
                    } else {
                        // integer_part is u64::MAX + 1, so has length 20
                        actual_w += 20;
                    }
                    // 4. The fractional part (if any):
                    if end > 0 {
                        let frac_part_w = f.precision().unwrap_or(pos);
                        actual_w += 1 + frac_part_w;
                    }

                    if requested_w <= actual_w {
                        // Output is already longer than `width`, so don't pad.
                        emit_without_padding(f)
                    } else {
                        // We need to add padding.
                        let post_padding_len = requested_w - actual_w;
                        emit_without_padding(f)?;
                        for _ in 0..post_padding_len {
                            f.write_char(f.fill())?;
                        }
                        Ok(())
                    }
                }
            }
        }

        // Print leading '+' sign if requested
        let prefix = if f.sign_plus() { "+" } else { "" };

        if self.gbps > 0 {
            fmt_decimal(f, self.gbps, self.bps.0, BPS_PER_GBPS / 10, prefix, "gbps")
        } else if self.bps.0 >= BPS_PER_MBPS {
            fmt_decimal(
                f,
                (self.bps.0 / BPS_PER_MBPS) as u64,
                self.bps.0 % BPS_PER_MBPS,
                BPS_PER_MBPS / 10,
                prefix,
                "mbps",
            )
        } else if self.bps.0 >= BPS_PER_KBPS {
            fmt_decimal(
                f,
                (self.bps.0 / BPS_PER_KBPS) as u64,
                self.bps.0 % BPS_PER_KBPS,
                BPS_PER_KBPS / 10,
                prefix,
                "kbps",
            )
        } else {
            fmt_decimal(f, self.bps.0 as u64, 0, 1, prefix, "bps")
        }
    }
}
