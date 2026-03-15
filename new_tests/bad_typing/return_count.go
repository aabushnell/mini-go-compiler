package main
import "fmt"

func pair() (int, int) {
    return 1    // returns 1 value but declares 2
}

func main() {
    a, b := pair()
    fmt.Print(a)
    fmt.Print(b)
    fmt.Print("\n")
}

