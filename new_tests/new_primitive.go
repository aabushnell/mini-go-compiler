package main
import "fmt"

func increment(p *int) {
    *p = *p + 1
}

func makeCounter(start int) *int {
    p := new(int)
    *p = start
    return p
}

func main() {
    // Basic allocation and zero-initialisation
    p := new(int)
    fmt.Print(*p)       // 0
    fmt.Print("\n")

    // Mutation through pointer
    *p = 42
    fmt.Print(*p)       // 42
    fmt.Print("\n")

    // Two pointers to independent heap locations
    q := new(int)
    *q = *p + 1
    fmt.Print(*p)       // 42
    fmt.Print("\n")
    fmt.Print(*q)       // 43
    fmt.Print("\n")

    // Passing pointer to function
    increment(p)
    fmt.Print(*p)       // 43
    fmt.Print("\n")

    // Returning pointer from function
    c := makeCounter(10)
    fmt.Print(*c)       // 10
    fmt.Print("\n")
    increment(c)
    fmt.Print(*c)       // 11
    fmt.Print("\n")

    // new(bool)
    b := new(bool)
    fmt.Print(*b)       // false
    fmt.Print("\n")
    *b = true
    fmt.Print(*b)       // true
    fmt.Print("\n")
}

