package main
import "fmt"

func main() {
    x := 5
    fmt.Print(*x)    // x is int, not a pointer
    fmt.Print("\n")
}

