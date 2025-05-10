def collatz(n):
    steps = 0
    while n != 1 and steps < 1000:
        if n % 2 == 0:
            n = n // 2
        else:
            n = 3 * n + 1
        steps += 1
    return n == 1

for n in range(1, 10000000001):
    if not collatz(n):
        print(f"Counterexample found at n={n}")
        break
else:
    print("No counterexamples found up to 10^10")