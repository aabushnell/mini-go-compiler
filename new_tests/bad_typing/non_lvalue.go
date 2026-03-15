package main
import "fmt"

func main() {
    p := &(1 + 2)    // 1+2 is not addressable
    fmt.Print(*p)
    fmt.Print("\n")
}

