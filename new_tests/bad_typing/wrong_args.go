package main
import "fmt"

func double(n int) int {
    return n + n
}

func main() {
    fmt.Print(double(true))    // bool passed where int expected
    fmt.Print("\n")
}

