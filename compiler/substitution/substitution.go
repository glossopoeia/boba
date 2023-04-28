package substitution

import (
	"github.com/glossopoeia/boba/compiler/kind"
	"github.com/glossopoeia/boba/compiler/types"
	"github.com/glossopoeia/boba/compiler/util"
)

type Substitution[T int | string] struct {
	Kinds map[T]kind.Kind[T]
	Types map[T]types.Type[T]
}

func (l Substitution[T]) Compose(fresh util.Fresh[T], r Substitution[T]) Substitution[T] {
	res := Substitution[T]{map[T]kind.Kind[T]{}, map[T]types.Type[T]{}}
	for v, k := range r.Kinds {
		res.Kinds[v] = KindSubst(l, k)
	}
	for v, k := range l.Kinds {
		res.Kinds[v] = k
	}
	for v, t := range r.Types {
		res.Types[v] = TypeSubst(fresh, l, t)
	}
	for v, t := range l.Types {
		res.Types[v] = t
	}
	return res
}
