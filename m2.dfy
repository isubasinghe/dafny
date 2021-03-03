function Fib(n: nat): nat
{
    if n < 2 then n else Fib(n-2) + Fib(n-1)
}


method ComputeFib(n: nat) returns (x: nat)
    ensures x == Fib(n)
{
    var i:= 0;
    x := 0;
    var y := 1;

    while i < n 
    invariant 0 <= i <= n
    invariant x == Fib(i) && y == Fib(i+1)
    {
        x, y := y, x+y;
        i := i + 1;
    }

}


function Sum(n:nat): nat
{
    if n == 0 then 0 else n + Sum(n-1)
}