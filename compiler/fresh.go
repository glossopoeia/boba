package compiler

import "fmt"

// Manages the generation of fresh variables, for use during e.g. type inference and
// unification. Note that while multiple instances of Fresh used in the same program
// will probably generate overlapping (i.e. non-fresh) variables.
//
// However, sometimes maintaining this invariant is unnecessary, so the functionality
// is not restricted to be a singleton.
type Fresh[T comparable] interface {
	// Return the next fresh variable. Will not overlap with previously generated variables.
	Next() T
	// Return the next N fresh variables. Will not overlap with previously generated variables.
	NextN(n int) []T
}

type IndexFresh struct {
	state int
}

type NameFresh struct {
	prefixes map[string]int
}

func (f *IndexFresh) Next() int {
	name := f.state
	f.state += 1
	return name
}

func (f *IndexFresh) NextN(n int) []int {
	res := make([]int, n)
	for i := 0; i < n; i++ {
		res[i] = f.Next()
	}
	return res
}

func NewNameFresh() NameFresh {
	return NameFresh{map[string]int{"?": 0}}
}

// Return the next fresh variable as a string name, prefixed with "?".
func (f *NameFresh) Next() string {
	name := fmt.Sprintf("?%d", f.prefixes["?"])
	f.prefixes["?"] += 1
	return name
}

func (f *NameFresh) NextN(n int) []string {
	res := make([]string, n)
	for i := 0; i < n; i++ {
		res[i] = f.Next()
	}
	return res
}

// Return the next fresh variable with the given prefix as a string name. Streams
// of prefixed fresh variables are maintained separately, so generating a fresh
// var for prefix "a" will not change the next value of the fresh var for prefix "b".
func (f *NameFresh) NextPrefix(prefix string) string {
	if preInd, ok := f.prefixes[prefix]; ok {
		f.prefixes[prefix] += 1
		return fmt.Sprintf("%s%d", prefix, preInd)
	}
	f.prefixes[prefix] = 0
	return fmt.Sprintf("%s0", prefix)
}
