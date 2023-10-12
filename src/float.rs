// Wrapper for a floating point that holds the upper and lower data as well as
// the floating point number. This could be done with some functions, but it is
// simpler to just hold the data like this. The only time it will be used is inside
// the vm operations to covert to and from floats.
use crate::data::Data;

#[derive(Debug, Clone)]
pub struct FloatPoint {
    pub upper: Data,
    pub lower: Data,
    pub float: f64,
}

impl FloatPoint {
    pub fn new(num: f64) -> FloatPoint {
        FloatPoint {
            upper: (i64::from_be_bytes(num.to_be_bytes()) >> 32) as Data,
            lower: i64::from_be_bytes(num.to_be_bytes()) as Data,
            float: num,
        }
    }

    pub fn from_data(upper: Data, lower: Data) -> FloatPoint {
        let num = ((upper as u64) << 32) | ((lower as u64) & 0xffff_ffff);
        FloatPoint {
            upper: upper,
            lower: lower,
            float: f64::from_be_bytes(num.to_be_bytes()),
        }
    }

    pub fn to_string(&self) -> String {
        format!("{:?}", self.float)
    }
}

// Testing ////////////////////////////////////////////////////////////////////
#[cfg(test)]
mod fixed_point_tests {
    use super::*;

    #[test]
    fn test_building_from_float() {
        let f = FloatPoint::new(1234.5678910);
        let f2 = FloatPoint::new(-1234.5678910);
        assert_eq!(f.upper, 1083394629);
        assert_eq!(f.lower, -2059935035);
        assert_eq!(f2.upper, -1064089019);
        assert_eq!(f2.lower, -2059935035);
    }

    #[test]
    fn test_building_from_parts() {
        let f = FloatPoint::from_data(1083394629, -2059935035);
        let f2 = FloatPoint::from_data(-1064089019, -2059935035);
        assert_eq!(f.float, 1234.5678910);
        assert_eq!(f2.float, -1234.5678910);
        let res = FloatPoint::new(f.float + f.float);
        assert_eq!(res.upper, 1084443205);
        assert_eq!(res.lower, -2059935035);
        assert_eq!(res.float, 2469.135782);
    }

    #[test]
    fn test_to_string() {
        let f = FloatPoint::new(1234.5678910);
        let f2 = FloatPoint::from_data(-1064089019, -2059935035);
        assert_eq!(f.to_string(), "1234.567891");
        assert_eq!(f2.to_string(), "-1234.567891");
    }
}
