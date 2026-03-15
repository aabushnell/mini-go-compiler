package main
import "fmt"

// Rewrite desugars:  a, b = b, a
// into:              var aux1; aux1 = b
//                    var aux2; aux2 = a
//                    a = aux1
//                    b = aux2
//
// With copy propagation ON:
//   aux1 = b  =>  env: { aux1=Copy(b) }
//   aux2 = a  =>  env: { aux1=Copy(b), aux2=Copy(a) }
//   a = aux1  =>  env: { ..., a=Copy(b) }
//   									-> emits a = b
//   b = aux2  =>  emits: b = a, but a = b at this point
//
func swapRuntime(a, b int) {
	a, b = b, a
	fmt.Print(a)
	fmt.Print("\n")
	fmt.Print(b)
	fmt.Print("\n")
}

// If both variables are statically known constants the problem is avoided
func swapConstants() {
	a := 10
	b := 20
	a, b = b, a
	fmt.Print(a)
	fmt.Print("\n")
	fmt.Print(b)
	fmt.Print("\n")
}

// Three-way rotation compounds the issue further
func rotateRuntime(a, b, c int) {
	a, b = b, a
	b, c = c, b
	fmt.Print(a)
	fmt.Print("\n")
	fmt.Print(b)
	fmt.Print("\n")
	fmt.Print(c)
	fmt.Print("\n")
}

func main() {
	fmt.Print("swapRuntime(10, 20):\n")
	swapRuntime(10, 20)
	// copy prop OFF: 20        copy prop ON:  20
	//                10                       20

	fmt.Print("swapConstants (10, 20):\n")
	swapConstants()
	// regardless of flag:
	//                20
	//                10

	fmt.Print("rotateRuntime(1, 2, 3):\n")
	rotateRuntime(1, 2, 3)
	// copy prop OFF:  2         copy prop ON:  2
	//                 3                        3
	//                 3                        3
	// expected: a=2, b=3, c=2
}

