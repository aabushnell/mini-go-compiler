package main
import "fmt"

type Node struct {
    value int
    next  Node    // value-type self-reference, infinite size
}

func main() {
    fmt.Print("hello")
    fmt.Print("\n")
}

