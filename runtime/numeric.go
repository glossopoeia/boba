package runtime

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
		if val.(uint8) < 0 {
			return -1
		} else if val.(uint8) > 0 {
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
		if val.(uint16) < 0 {
			return -1
		} else if val.(uint16) > 0 {
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
		if val.(uint32) < 0 {
			return -1
		} else if val.(uint32) > 0 {
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
		if val.(uint64) < 0 {
			return -1
		} else if val.(uint64) > 0 {
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
		if val.(uint) < 0 {
			return -1
		} else if val.(uint) > 0 {
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
