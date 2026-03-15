package main
import "fmt"

func main() {
    x := 1
    if x {           // int is not a valid condition
        fmt.Print("yes")
        fmt.Print("\n")
    }
}

