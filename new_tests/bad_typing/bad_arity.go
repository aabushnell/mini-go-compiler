package main
import "fmt"

func pair() (int, int) {
    return 1, 2
}

func main() {
    a, b, c := pair()    // 3 variables, 2 return values
    fmt.Print(a)
    fmt.Print(b)
    fmt.Print(c)
    fmt.Print("\n")
}

