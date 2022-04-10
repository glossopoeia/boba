package runtime

import "math"

func Negate(instr Instruction, val Value) Value {
	switch instr {
	case I8:
		return -val.(int8)
	case U8:
		return -val.(uint8)
	case I16:
		return -val.(int16)
	case U16:
		return -val.(uint16)
	case I32:
		return -val.(int32)
	case U32:
		return -val.(uint32)
	case I64:
		return -val.(int64)
	case U64:
		return -val.(uint64)
	case INATIVE:
		return -val.(int)
	case UNATIVE:
		return -val.(uint)
	case SINGLE:
		return -val.(float32)
	case DOUBLE:
		return -val.(float64)
	default:
		panic("Invalid negation argument type.")
	}
}

func Increment(instr Instruction, val Value) Value {
	switch instr {
	case I8:
		return val.(int8) + 1
	case U8:
		return val.(uint8) + 1
	case I16:
		return val.(int16) + 1
	case U16:
		return val.(uint16) + 1
	case I32:
		return val.(int32) + 1
	case U32:
		return val.(uint32) + 1
	case I64:
		return val.(int64) + 1
	case U64:
		return val.(uint64) + 1
	case INATIVE:
		return val.(int) + 1
	case UNATIVE:
		return val.(uint) + 1
	case SINGLE:
		return val.(float32) + 1
	case DOUBLE:
		return val.(float64) + 1
	default:
		panic("Invalid negation argument type.")
	}
}

func Decrement(instr Instruction, val Value) Value {
	switch instr {
	case I8:
		return val.(int8) - 1
	case U8:
		return val.(uint8) - 1
	case I16:
		return val.(int16) - 1
	case U16:
		return val.(uint16) - 1
	case I32:
		return val.(int32) - 1
	case U32:
		return val.(uint32) - 1
	case I64:
		return val.(int64) - 1
	case U64:
		return val.(uint64) - 1
	case INATIVE:
		return val.(int) - 1
	case UNATIVE:
		return val.(uint) - 1
	case SINGLE:
		return val.(float32) - 1
	case DOUBLE:
		return val.(float64) - 1
	default:
		panic("Invalid negation argument type.")
	}
}

func Add(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) + r.(int8)
	case U8:
		return l.(uint8) + r.(uint8)
	case I16:
		return l.(int16) + r.(int16)
	case U16:
		return l.(uint16) + r.(uint16)
	case I32:
		return l.(int32) + r.(int32)
	case U32:
		return l.(uint32) + r.(uint32)
	case I64:
		return l.(int64) + r.(int64)
	case U64:
		return l.(uint64) + r.(uint64)
	case INATIVE:
		return l.(int) + r.(int)
	case UNATIVE:
		return l.(uint) + r.(uint)
	case SINGLE:
		return l.(float32) + r.(float32)
	case DOUBLE:
		return l.(float64) + r.(float64)
	default:
		panic("Invalid addition argument type.")
	}
}

func Subtract(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) - r.(int8)
	case U8:
		return l.(uint8) - r.(uint8)
	case I16:
		return l.(int16) - r.(int16)
	case U16:
		return l.(uint16) - r.(uint16)
	case I32:
		return l.(int32) - r.(int32)
	case U32:
		return l.(uint32) - r.(uint32)
	case I64:
		return l.(int64) - r.(int64)
	case U64:
		return l.(uint64) - r.(uint64)
	case INATIVE:
		return l.(int) - r.(int)
	case UNATIVE:
		return l.(uint) - r.(uint)
	case SINGLE:
		return l.(float32) - r.(float32)
	case DOUBLE:
		return l.(float64) - r.(float64)
	default:
		panic("Invalid subtraction argument type.")
	}
}

func Multiply(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) * r.(int8)
	case U8:
		return l.(uint8) * r.(uint8)
	case I16:
		return l.(int16) * r.(int16)
	case U16:
		return l.(uint16) * r.(uint16)
	case I32:
		return l.(int32) * r.(int32)
	case U32:
		return l.(uint32) * r.(uint32)
	case I64:
		return l.(int64) * r.(int64)
	case U64:
		return l.(uint64) * r.(uint64)
	case INATIVE:
		return l.(int) * r.(int)
	case UNATIVE:
		return l.(uint) * r.(uint)
	case SINGLE:
		return l.(float32) * r.(float32)
	case DOUBLE:
		return l.(float64) * r.(float64)
	default:
		panic("Invalid multiply argument type.")
	}
}

func DivRemT(instr Instruction, l Value, r Value) (Value, Value) {
	switch instr {
	case I8:
		return l.(int8) / r.(int8), l.(int8) % r.(int8)
	case U8:
		return l.(uint8) / r.(uint8), l.(uint8) % r.(uint8)
	case I16:
		return l.(int16) / r.(int16), l.(int16) % r.(int16)
	case U16:
		return l.(uint16) / r.(uint16), l.(uint16) % r.(uint16)
	case I32:
		return l.(int32) / r.(int32), l.(int32) % r.(int32)
	case U32:
		return l.(uint32) / r.(uint32), l.(uint32) % r.(uint32)
	case I64:
		return l.(int64) / r.(int64), l.(int64) % r.(int64)
	case U64:
		return l.(uint64) / r.(uint64), l.(uint64) % r.(uint64)
	case INATIVE:
		return l.(int) / r.(int), l.(int) % r.(int)
	case UNATIVE:
		return l.(uint) / r.(uint), l.(uint) % r.(uint)
	case SINGLE:
		return l.(float32) / r.(float32), float32(math.Mod(float64(l.(float32)), float64(r.(float32))))
	case DOUBLE:
		return l.(float64) / r.(float64), math.Mod(l.(float64), r.(float64))
	default:
		panic("Invalid divremt argument type.")
	}
}

func DivRemF(instr Instruction, l Value, r Value) (Value, Value) {
	switch instr {
	case I8:
		quot, rem := l.(int8)/r.(int8), l.(int8)%r.(int8)
		if (rem > 0 && r.(int8) < 0) || (rem < 0 && r.(int8) > 0) {
			quot = quot - 1
			rem = rem + r.(int8)
		}
		return quot, rem
	case U8:
		return l.(uint8) / r.(uint8), l.(uint8) % r.(uint8)
	case I16:
		quot, rem := l.(int16)/r.(int16), l.(int16)%r.(int16)
		if (rem > 0 && r.(int16) < 0) || (rem < 0 && r.(int16) > 0) {
			quot = quot - 1
			rem = rem + r.(int16)
		}
		return quot, rem
	case U16:
		return l.(uint16) / r.(uint16), l.(uint16) % r.(uint16)
	case I32:
		quot, rem := l.(int32)/r.(int32), l.(int32)%r.(int32)
		if (rem > 0 && r.(int32) < 0) || (rem < 0 && r.(int32) > 0) {
			quot = quot - 1
			rem = rem + r.(int32)
		}
		return quot, rem
	case U32:
		return l.(uint32) / r.(uint32), l.(uint32) % r.(uint32)
	case I64:
		quot, rem := l.(int64)/r.(int64), l.(int64)%r.(int64)
		if (rem > 0 && r.(int64) < 0) || (rem < 0 && r.(int64) > 0) {
			quot = quot - 1
			rem = rem + r.(int64)
		}
		return quot, rem
	case U64:
		return l.(uint64) / r.(uint64), l.(uint64) % r.(uint64)
	case INATIVE:
		quot, rem := l.(int)/r.(int), l.(int)%r.(int)
		if (rem > 0 && r.(int) < 0) || (rem < 0 && r.(int) > 0) {
			quot = quot - 1
			rem = rem + r.(int)
		}
		return quot, rem
	case UNATIVE:
		return l.(uint) / r.(uint), l.(uint) % r.(uint)
	case SINGLE:
		panic("divremf does not yet support float32 type.")
	case DOUBLE:
		panic("divremf does not yet support float64 type.")
	default:
		panic("Invalid divremf argument type.")
	}
}

func DivRemE(instr Instruction, l Value, r Value) (Value, Value) {
	switch instr {
	case I8:
		quot, rem := l.(int8)/r.(int8), l.(int8)%r.(int8)
		if rem < 0 {
			if r.(int8) > 0 {
				quot = quot - 1
				rem = rem + r.(int8)
			} else {
				quot = quot + 1
				rem = rem - r.(int8)
			}
		}
		return quot, rem
	case U8:
		return l.(uint8) / r.(uint8), l.(uint8) % r.(uint8)
	case I16:
		quot, rem := l.(int16)/r.(int16), l.(int16)%r.(int16)
		if rem < 0 {
			if r.(int16) > 0 {
				quot = quot - 1
				rem = rem + r.(int16)
			} else {
				quot = quot + 1
				rem = rem - r.(int16)
			}
		}
		return quot, rem
	case U16:
		return l.(uint16) / r.(uint16), l.(uint16) % r.(uint16)
	case I32:
		quot, rem := l.(int32)/r.(int32), l.(int32)%r.(int32)
		if rem < 0 {
			if r.(int32) > 0 {
				quot = quot - 1
				rem = rem + r.(int32)
			} else {
				quot = quot + 1
				rem = rem - r.(int32)
			}
		}
		return quot, rem
	case U32:
		return l.(uint32) / r.(uint32), l.(uint32) % r.(uint32)
	case I64:
		quot, rem := l.(int64)/r.(int64), l.(int64)%r.(int64)
		if rem < 0 {
			if r.(int64) > 0 {
				quot = quot - 1
				rem = rem + r.(int64)
			} else {
				quot = quot + 1
				rem = rem - r.(int64)
			}
		}
		return quot, rem
	case U64:
		return l.(uint64) / r.(uint64), l.(uint64) % r.(uint64)
	case INATIVE:
		quot, rem := l.(int)/r.(int), l.(int)%r.(int)
		if rem < 0 {
			if r.(int) > 0 {
				quot = quot - 1
				rem = rem + r.(int)
			} else {
				quot = quot + 1
				rem = rem - r.(int)
			}
		}
		return quot, rem
	case UNATIVE:
		return l.(uint) / r.(uint), l.(uint) % r.(uint)
	case SINGLE:
		panic("divreme does not yet support float32 types.")
	case DOUBLE:
		panic("divreme does not yet support float64 types.")
	default:
		panic("Invalid divreme argument type.")
	}
}

func BitwiseOr(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) | r.(int8)
	case U8:
		return l.(uint8) | r.(uint8)
	case I16:
		return l.(int16) | r.(int16)
	case U16:
		return l.(uint16) | r.(uint16)
	case I32:
		return l.(int32) | r.(int32)
	case U32:
		return l.(uint32) | r.(uint32)
	case I64:
		return l.(int64) | r.(int64)
	case U64:
		return l.(uint64) | r.(uint64)
	case INATIVE:
		return l.(int) | r.(int)
	case UNATIVE:
		return l.(uint) | r.(uint)
	default:
		panic("Invalid bitwise or argument type.")
	}
}

func BitwiseAnd(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) & r.(int8)
	case U8:
		return l.(uint8) & r.(uint8)
	case I16:
		return l.(int16) & r.(int16)
	case U16:
		return l.(uint16) & r.(uint16)
	case I32:
		return l.(int32) & r.(int32)
	case U32:
		return l.(uint32) & r.(uint32)
	case I64:
		return l.(int64) & r.(int64)
	case U64:
		return l.(uint64) & r.(uint64)
	case INATIVE:
		return l.(int) & r.(int)
	case UNATIVE:
		return l.(uint) & r.(uint)
	default:
		panic("Invalid bitwise and argument type.")
	}
}

func BitwiseXor(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) ^ r.(int8)
	case U8:
		return l.(uint8) ^ r.(uint8)
	case I16:
		return l.(int16) ^ r.(int16)
	case U16:
		return l.(uint16) ^ r.(uint16)
	case I32:
		return l.(int32) ^ r.(int32)
	case U32:
		return l.(uint32) ^ r.(uint32)
	case I64:
		return l.(int64) ^ r.(int64)
	case U64:
		return l.(uint64) ^ r.(uint64)
	case INATIVE:
		return l.(int) ^ r.(int)
	case UNATIVE:
		return l.(uint) ^ r.(uint)
	default:
		panic("Invalid bitwise xor argument type.")
	}
}

func Complement(instr Instruction, val Value) Value {
	switch instr {
	case I8:
		return ^val.(int8)
	case U8:
		return ^val.(uint8)
	case I16:
		return ^val.(int16)
	case U16:
		return ^val.(uint16)
	case I32:
		return ^val.(int32)
	case U32:
		return ^val.(uint32)
	case I64:
		return ^val.(int64)
	case U64:
		return ^val.(uint64)
	case INATIVE:
		return ^val.(int)
	case UNATIVE:
		return ^val.(uint)
	default:
		panic("Invalid bitwise xor argument type.")
	}
}

func ShiftLeft(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) << r.(int8)
	case U8:
		return l.(uint8) << r.(uint8)
	case I16:
		return l.(int16) << r.(int16)
	case U16:
		return l.(uint16) << r.(uint16)
	case I32:
		return l.(int32) << r.(int32)
	case U32:
		return l.(uint32) << r.(uint32)
	case I64:
		return l.(int64) << r.(int64)
	case U64:
		return l.(uint64) << r.(uint64)
	case INATIVE:
		return l.(int) << r.(int)
	case UNATIVE:
		return l.(uint) << r.(uint)
	default:
		panic("Invalid shift left argument type.")
	}
}

func ShiftRight(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) >> r.(int8)
	case U8:
		return l.(uint8) >> r.(uint8)
	case I16:
		return l.(int16) >> r.(int16)
	case U16:
		return l.(uint16) >> r.(uint16)
	case I32:
		return l.(int32) >> r.(int32)
	case U32:
		return l.(uint32) >> r.(uint32)
	case I64:
		return l.(int64) >> r.(int64)
	case U64:
		return l.(uint64) >> r.(uint64)
	case INATIVE:
		return l.(int) >> r.(int)
	case UNATIVE:
		return l.(uint) >> r.(uint)
	default:
		panic("Invalid shift right argument type.")
	}
}

func Equal(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) == r.(int8)
	case U8:
		return l.(uint8) == r.(uint8)
	case I16:
		return l.(int16) == r.(int16)
	case U16:
		return l.(uint16) == r.(uint16)
	case I32:
		return l.(int32) == r.(int32)
	case U32:
		return l.(uint32) == r.(uint32)
	case I64:
		return l.(int64) == r.(int64)
	case U64:
		return l.(uint64) == r.(uint64)
	case INATIVE:
		return l.(int) == r.(int)
	case UNATIVE:
		return l.(uint) == r.(uint)
	case SINGLE:
		return l.(float32) == r.(float32)
	case DOUBLE:
		return l.(float64) == r.(float64)
	default:
		panic("Invalid multiply argument type.")
	}
}

func LessThan(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) < r.(int8)
	case U8:
		return l.(uint8) < r.(uint8)
	case I16:
		return l.(int16) < r.(int16)
	case U16:
		return l.(uint16) < r.(uint16)
	case I32:
		return l.(int32) < r.(int32)
	case U32:
		return l.(uint32) < r.(uint32)
	case I64:
		return l.(int64) < r.(int64)
	case U64:
		return l.(uint64) < r.(uint64)
	case INATIVE:
		return l.(int) < r.(int)
	case UNATIVE:
		return l.(uint) < r.(uint)
	case SINGLE:
		return l.(float32) < r.(float32)
	case DOUBLE:
		return l.(float64) < r.(float64)
	default:
		panic("Invalid multiply argument type.")
	}
}

func GreaterThan(instr Instruction, l Value, r Value) Value {
	switch instr {
	case I8:
		return l.(int8) > r.(int8)
	case U8:
		return l.(uint8) > r.(uint8)
	case I16:
		return l.(int16) > r.(int16)
	case U16:
		return l.(uint16) > r.(uint16)
	case I32:
		return l.(int32) > r.(int32)
	case U32:
		return l.(uint32) > r.(uint32)
	case I64:
		return l.(int64) > r.(int64)
	case U64:
		return l.(uint64) > r.(uint64)
	case INATIVE:
		return l.(int) > r.(int)
	case UNATIVE:
		return l.(uint) > r.(uint)
	case SINGLE:
		return l.(float32) > r.(float32)
	case DOUBLE:
		return l.(float64) > r.(float64)
	default:
		panic("Invalid multiply argument type.")
	}
}

func Sign(instr Instruction, val Value) Value {
	switch instr {
	case I8:
		if val.(int8) < 0 {
			return -1
		} else if val.(int8) > 0 {
			return 1
		} else {
			return 0
		}
	case U8:
		if val.(uint8) > 0 {
			return 1
		} else {
			return 0
		}
	case I16:
		if val.(int16) < 0 {
			return -1
		} else if val.(int16) > 0 {
			return 1
		} else {
			return 0
		}
	case U16:
		if val.(uint16) > 0 {
			return 1
		} else {
			return 0
		}
	case I32:
		if val.(int32) < 0 {
			return -1
		} else if val.(int32) > 0 {
			return 1
		} else {
			return 0
		}
	case U32:
		if val.(uint32) > 0 {
			return 1
		} else {
			return 0
		}
	case I64:
		if val.(int64) < 0 {
			return -1
		} else if val.(int64) > 0 {
			return 1
		} else {
			return 0
		}
	case U64:
		if val.(uint64) > 0 {
			return 1
		} else {
			return 0
		}
	case INATIVE:
		if val.(int) < 0 {
			return -1
		} else if val.(int) > 0 {
			return 1
		} else {
			return 0
		}
	case UNATIVE:
		if val.(uint) > 0 {
			return 1
		} else {
			return 0
		}
	case SINGLE:
		if val.(float32) < 0 {
			return -1
		} else if val.(float32) > 0 {
			return 1
		} else {
			return 0
		}
	case DOUBLE:
		if val.(float64) < 0 {
			return -1
		} else if val.(float64) > 0 {
			return 1
		} else {
			return 0
		}
	default:
		panic("Invalid multiply argument type.")
	}
}

func convertBool(val bool, to Instruction) Value {
	switch to {
	case BOOL:
		return bool(val)
	case I8:
		if val {
			return int8(1)
		} else {
			return int8(0)
		}
	case U8:
		if val {
			return uint8(1)
		} else {
			return uint8(0)
		}
	case I16:
		if val {
			return int16(1)
		} else {
			return int16(0)
		}
	case U16:
		if val {
			return uint16(1)
		} else {
			return uint16(0)
		}
	case I32:
		if val {
			return int32(1)
		} else {
			return int32(0)
		}
	case U32:
		if val {
			return uint32(1)
		} else {
			return uint32(0)
		}
	case I64:
		if val {
			return int64(1)
		} else {
			return int64(0)
		}
	case U64:
		if val {
			return uint64(1)
		} else {
			return uint64(0)
		}
	case INATIVE:
		if val {
			return int(1)
		} else {
			return int(0)
		}
	case UNATIVE:
		if val {
			return uint(1)
		} else {
			return uint(0)
		}
	case SINGLE:
		if val {
			return float32(1)
		} else {
			return float32(0)
		}
	case DOUBLE:
		if val {
			return float64(1)
		} else {
			return float64(0)
		}
	default:
		panic("Unknown value type")
	}
}

func convertI8(val int8, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertU8(val uint8, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertI16(val int16, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertU16(val uint16, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertI32(val int32, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertU32(val uint32, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertI64(val int64, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertU64(val uint64, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertINative(val int, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertUNative(val uint, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertSingle(val float32, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}

func convertDouble(val float64, to Instruction) Value {
	switch to {
	case BOOL:
		if val == 0 {
			return false
		} else {
			return true
		}
	case I8:
		return int8(val)
	case U8:
		return uint8(val)
	case I16:
		return int16(val)
	case U16:
		return uint16(val)
	case I32:
		return int32(val)
	case U32:
		return uint32(val)
	case I64:
		return int64(val)
	case U64:
		return uint64(val)
	case INATIVE:
		return int(val)
	case UNATIVE:
		return uint(val)
	case SINGLE:
		return float32(val)
	case DOUBLE:
		return float64(val)
	default:
		panic("Unknown value type")
	}
}
