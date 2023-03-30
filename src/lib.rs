use std::{collections::HashMap, ops};

#[macro_export]
macro_rules! ValueUnit {
    ($value:literal $($unit:ident$(^$power:literal)?)*) => {
        ValueUnit::new($value, std::collections::HashMap::from([$((stringify!($unit).to_string(), 1 $(-1+$power)?),)*]))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValueUnit {
    pub value: f64,
    units: HashMap<String, i8>
}

impl ops::Add<&ValueUnit> for &ValueUnit {
    fn add(self, other: &ValueUnit) -> ValueUnit {
        assert_eq!(self.units, other.units, "{} does not equal {}", self.units_to_string(), other.units_to_string());
        return ValueUnit { value: self.value + other.value, units: self.units.clone() }
    }

    type Output = ValueUnit;
}

impl ops::AddAssign<&ValueUnit> for ValueUnit {
    fn add_assign(&mut self, other: &ValueUnit) {
        assert_eq!(self.units, other.units, "{} does not equal {}", self.units_to_string(), other.units_to_string());
        self.value += other.value;
    }
}

impl ops::Sub<&ValueUnit> for &ValueUnit {
    fn sub(self, other: &ValueUnit) -> ValueUnit {
        assert_eq!(self.units, other.units, "{} does not equal {}", self.units_to_string(), other.units_to_string());
        return ValueUnit { value: self.value - other.value, units: self.units.clone() }
    }

    type Output = ValueUnit;
}

impl ops::Mul<f64> for &ValueUnit {
    fn mul(self, other: f64) -> ValueUnit {
        return ValueUnit { value: self.value * other, units: self.units.clone() }
    }

    type Output = ValueUnit;
}

impl ops::Mul<&ValueUnit> for &ValueUnit {
    fn mul(self, other: &ValueUnit) -> ValueUnit {
        let mut res_units: HashMap<String, i8> = self.units.clone();
        for (key, value) in other.units.clone() {
            if let Some(existing_value) = res_units.get_mut(&key) {
                *existing_value += value;
            } else {
                res_units.insert(key.to_string(), value);
            }
        }
        res_units.retain(|_, v| *v != 0);
        return ValueUnit { value: self.value * other.value, units: res_units }
    }

    type Output = ValueUnit;
}

impl ops::Div<f64> for &ValueUnit {
    fn div(self, other: f64) -> ValueUnit {
        return ValueUnit { value: self.value / other, units: self.units.clone() }
    }

    type Output = ValueUnit;
}

impl ops::Div<&ValueUnit> for &ValueUnit {
    fn div(self, other: &ValueUnit) -> ValueUnit {
        let mut res_units: HashMap<String, i8> = self.units.clone();
        for (key, value) in other.units.clone() {
            if let Some(existing_value) = res_units.get_mut(&key) {
                *existing_value -= value;
            } else {
                res_units.insert(key.to_string(), -value);
            }
        }
        res_units.retain(|_, v| *v != 0);
        return ValueUnit { value: self.value / other.value, units: res_units }
    }

    type Output = ValueUnit;
}

impl ValueUnit {
    pub fn new(value: f64, units: HashMap<String, i8>) -> Self {
        Self { value, units }
    }
    fn units_to_string(&self) -> String {
        return self.units.iter().fold("".to_string(), |acc, (k, v)| {
            if acc == "".to_string() {
                if *v == 1 {
                    return k.to_string();
                } else {
                    return format!("{k}^{v}")
                }
            } else {
                if *v == 1 {
                    return format!("{acc} {k}")
                } else {
                    return format!("{acc} {k}^{v}")
                }
            }
        });
    }
    pub fn pow(&self, power: i8) -> Self {
        return Self { value: self.value.powi(power as i32), units: HashMap::from_iter(self.units.iter().map(|(k,v)| (k.clone(), v * power))) }
    }
    pub fn root(&self, root: i8) -> Self {
        return Self { value: self.value.powf(1.0 / (root as f64)), units: HashMap::from_iter(self.units.iter().map(|(k,v)| {
            assert_eq!(v % root, 0, "{v} must be divisible by {root}");
            return (k.clone(), v / root);
        })) }
    }
}

impl TryFrom<String> for ValueUnit {
    fn try_from(constructor: String) -> Result<Self, Self::Error> {
        let mut constructor_iter = constructor.trim().split_ascii_whitespace();
        let value_str = constructor_iter.next().unwrap();
        let value = match value_str.parse() {
            Ok(value) => value,
            Err(_) => return Err("Not a valid value")
        };
        let units: HashMap<String, i8> = constructor_iter.map(|unit_and_power| {
            if unit_and_power.contains('^') {
                let mut unit_and_power_iter = unit_and_power.split('^');
                let unit = unit_and_power_iter.next().unwrap();
                let power_str = unit_and_power_iter.next().unwrap();
                let power = match power_str.parse() {
                    Ok(poweri8) => poweri8,
                    Err(_) => return Err("Not a valid power")
                };
                return Ok((unit.to_string(), power))
            } else {
                return Ok((unit_and_power.to_string(), 1));
            }
        }).collect::<Result<HashMap<String, i8>, &'static str>>()?;
        Ok(ValueUnit { value, units })
    }

    type Error = &'static str;
}

impl std::fmt::Display for ValueUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.value, self.units_to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eq() {
        assert_eq!(ValueUnit!(1.0 kg), ValueUnit!(1.0 kg));
        assert_ne!(ValueUnit!(1.0 kg), ValueUnit!(2.0 kg));
    }
    #[test]
    fn add() {
        let result = &ValueUnit!(4.0 kg m^-3) + &ValueUnit!(5.0 kg m^-3);
        assert_eq!(result, ValueUnit!(9.0 kg m^-3));
    }
    #[test]
    fn sub() {
        let result = &ValueUnit!(4.0 kg m^-3) - &ValueUnit!(5.0 kg m^-3);
        assert_eq!(result, ValueUnit!(-1.0 kg m^-3));
    }
    #[test]
    fn mul_self() {
        let result = &ValueUnit!(4.0 kg) * &ValueUnit!(5.0 m s^-2);
        assert_eq!(result, ValueUnit!(20.0 kg m s^-2));
    }
    #[test]
    fn div_self() {
        let result = &ValueUnit!(4.0 kg) / &ValueUnit!(5.0 m^3);
        assert_eq!(result, ValueUnit!(0.8 kg m^-3));
    }
    #[test]
    fn mul_f64() {
        let result = &ValueUnit!(4.0 kg) * 5.0;
        assert_eq!(result, ValueUnit!(20.0 kg));
    }
    #[test]
    fn div_f64() {
        let result = &ValueUnit!(4.0 kg) / 5.0;
        assert_eq!(result, ValueUnit!(0.8 kg));
    }
    #[test]
    fn add_assign() {
        let mut result = ValueUnit!(4.0 kg m^-3);
        result += &ValueUnit!(5.0 kg m^-3);
        assert_eq!(result, ValueUnit!(9.0 kg m^-3));
    }
    #[test]
    fn root() {
        let result = ValueUnit!(8.0 m^3).root(3);
        assert_eq!(result, ValueUnit!(2.0 m));
    }
    #[test]
    fn pow() {
        let result = ValueUnit!(2.0 m).pow(3);
        assert_eq!(result, ValueUnit!(8.0 m^3));
        let result2 = ValueUnit!(2.0 m).pow(2);
        assert_eq!(result2, ValueUnit!(4.0 m^2));
    }
    #[test]
    fn from_string() {
        let result: Result<ValueUnit, &str> = ValueUnit::try_from("10 kg ".to_string());
        assert_eq!(result, Ok(ValueUnit!(10.0 kg)));
        let result: Result<ValueUnit, &str> = "10 kg m^3 s^-2 ".to_string().try_into();
        assert_eq!(result, Ok(ValueUnit!(10.0 kg m^3 s^-2)));
        let result: Result<ValueUnit, &str> = "x kg m^3 s^-2".to_string().try_into();
        assert_eq!(result, Err("Not a valid value"));
        let result: Result<ValueUnit, &str> = "10 kg m^x s^-2".to_string().try_into();
        assert_eq!(result, Err("Not a valid power"));
    }
}