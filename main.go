/*
Copyright © 2023 Glossopoeia
*/
package main

import (
	"fmt"

	"github.com/glossopoeia/boba/cmd"
	"github.com/glossopoeia/boba/compiler"
)

func main() {
	fmt.Printf("%s", compiler.SynKVar("a"))
	cmd.Execute()
}
