package main
import "fmt"

func main() {
    if nil == nil {    // Go spec forbids this
        fmt.Print("equal")
        fmt.Print("\n")
    }
}

