package main
import "fmt"

func sign(n int) int {
    if n > 0 {
        return 1
    }
    // missing return for n <= 0 case
}

func main() {
    fmt.Print(sign(5))
    fmt.Print("\n")
}

