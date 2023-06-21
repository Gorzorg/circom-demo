pragma circom 2.0.0;

/*
In this demo, you will be introduced to circom, and will be shown how it works with practical code examples.
Circom is a hardware description language. Our goal is to "build circuits", and the language provides
basically two kinds of instructions.

The first kind of instruction is very restricted, and is involved with actually building the circuit.
With this kind of instructions one can declare "signals", "components", and one can "add wires" to the circuit.

The second kind of instruction is much more general, and it is involved with
computing the missing inputs of a circuit. For example, if the circuit has 3 signals, of which
two are an input to the circuit, and the other one is an output,
and if the user is only supposed to provide one of those inputs, circom allows you to compute
what the other input should be in order to obtain the desired output
(or in order to simply prevent a program crash during proof generation, more on that later)

Here is a sketch of what happens with a circom program:
- The program is compiled into a bunch of output files
- Some of the files are used to compute the private inputs given the public inputs (the so called "witness")
- Some of the files are used to compute, given a public input, a witness,
    and some circuit-dependent public parameters, a zero knowledge proof of the coherence of the circuit
    (i.e. that the output actually is the product of the public input, and of a valid witness)

As a basic example, one could say

    This circuit has public input a, private input b, and output c = SHA256(a ^ SHA256(b)).
    
    I know how to set a and b such that the output equals some number x that i am publishing.

    I write (a, b) in a file, and i make circom compute the rest of the witness
    (i.e. mostly intermediate computations that nobody cares about, that roughly act as auxiliary inputs)

    Then I prompt a snark prover to compute the proof, given
    (a, b, rest of the witness, compiled circom program, public parameters)
    as input.

    Then I publish (a, x, proof) for everyone (who already knows the circuit) to check.
*/

// Keep in mind that in circom every variable is a remainder class modulo p,
// where p is a huge prime number p.
// The language provides the abstractions for vectors and for loops,
// but only when the sizes and iteration numbers can be unrolled at compile time.

// Also, throughout this file we use the convention that the boolean values are represented as follows:
// 1 == true
// 0 == false
// Every other value which is not 0 or 1 does not represent a boolean value.
// We call this convention boolean standard form.

/*
Without further ado, let's introduce one of the simplest circuits imaginable:
Given an input,
let's make the circuit output 0 if the input is 0,
and let's make the circuit output 1 otherwise.

How hard could it be?
*/

// given an input `in`, computes `in != 0`, and outputs it in boolean standard form
// UNSAFE!
// can you guess why?
template IsNotZeroUnsafe() {
    // When we want to declare a signal in the circuit, we have to use a syntax like
    // signal [optionally input/output] label.
    // The inputs are specified by the user, or they are fed from a bigger circuit into this one
    // The outputs can be read by the public, or they can be used by some bigger circuit
    // The signals without an input/output tag are just part of the automatically computed witness,
    //     and basically serve as helper values in the computations of the circuit
    signal input in;

    // We have to tell circom how to assign the witness,
    // otherwise it doesn't have a way to compute it, because it is not part of user input.
    // One can assign a value to a signal using the syntax
    //
    // label <-- expression;
    //
    // Where expression can be any general computation. In this case, we want a signal to be one,
    // and we want a signal to be either 0 or 1, depending on the value of the signal `in`.
    signal one <-- 1;
    signal output is_not_zero <-- (in != 0) ? 1 : 0;

    // When we want to "set the wires of the circuit", we use the "===" operator.
    // This operator is what decides what gets proved, and what doesn't.
    (1 - is_not_zero) * in === 0;

    // Remember:
    // If one writes a perfectly valid sequence of "<--" instructions, so that the witness is computed perfectly,
    // but then forgets to add the "===" instructions, then the resulting proof will be buggy,
    // because a malicious user could compute a malicious witness (using a custom program instead of circom's output)
    // and this malicious witness would then be validated by the prover,
    // because the circuit does not check the constraints on the various signals.
    //
    // Can you spot how a malicious user could generate a wrong witness for this circuit?
}




// While the above circuit produces correct proofs if in != 0,
// nobody ensures that a malicious prover will set is_not_zero in the correct way.
// A malicious prover could do
//
// is_not_zero <-- in
//
// even when in == 0, effectively producing a proof that 0 != 0.
// Here follows a safe version.

/*
It must be noted that the "===" operator is very limited. It cannot check all kinds of relations, but only
the expressions of the type

A * B === C, where A, B, C are of the form
k_1 * sig_1 + ... + k_n * sig_n, where
k_1, ..., k_n are integer coefficients, and where
sig_1, ..., sig_n are signals.

This severely constrains the way we can check various conditions.
A classic exmample is if we want to check that, given two signals a and b, it holds

a * a * a === b.

This would give an error. What we must do instead is:
We declare a helper signal c, and then we write

a * a === c;
a * c === b;

Armed with this knowledge, we proceed to the correct way to implement IsNotZero
*/

// This template computes in != 0, and outputs it in boolean standard form.
template IsNotZero() {
    // As before, we declare an input signal
    signal input in;

    // As before, we declare an output signal, and tell circom how to set it
    signal output is_not_zero <-- (in != 0) ? 1 : 0;
    // But we also enforce `is_not_zero` to be either 0 or 1.
    is_not_zero * (is_not_zero - 1) === 0;

    // This signal does not have an analogue in the unsafe template!
    //
    // if `in` is not zero, we compute its inverse,
    // otherwise we assign zero to this signal
    //
    // We are going to use that, modulo a prime number, only the 0 number does not have an inverse.
    // This means that, if we are able to show an inverse, then the input was not zero to begin with.
    signal inverse <-- (in != 0) ? 1/in : 0;

    

    // We enforce that, if is_not_zero == 1, then in * inverse == 1, which implies in != 0
    in * inverse === is_not_zero;
    // We enforce that, if is_not_zero == 0, then in == 0.
    (1 - is_not_zero) * in === 0;
}

// given an input `in`, computes `in == 0`, and outputs it in boolean standard form.
template IsZero() {
    signal input in;

    signal output is_zero <-- (in == 0) ? 1 : 0;

    // In order to force the boolean standard form, we impose that the 
    is_zero * (is_zero - 1) === 0;

    signal inverse <-- (in != 0) ? 1 / in : 0;
    in * inverse === 1 - is_zero;
    is_zero * in === 0;
}

//Computes a == b, and outputs it in boolean standard form.
template IsEqual() {
    signal input a;
    signal input b;
    signal output out;
    component c = IsZero();
    c.in <== a - b;
    out <== c.is_zero;
}

//Computes a != b, and outputs it in boolean standard form.
template IsNotEqual() {
    signal input a;
    signal input b;
    signal output out;
    component c = IsNotZero();
    c.in <== a - b;
    out <== c.is_not_zero;
}

// What about proving elementary logic gates?
//
// From now on, we use the convention that
// every non-zero number represents "true", and 0 represents "false".

// Assumes that a and b represent booleans in standard form.
//Computes a && b, and outputs it in boolean standard form.
template AND() {
    signal input a;
    signal input b;
    signal output out <== a * b;
}

// Assumes that a and b represent booleans in standard form.
//Computes a || b, and outputs it in boolean standard form.
template OR() {
    signal input a;
    signal input b;
    signal output out <== a + b - a * b;
}

// Assumes that a and b represent booleans in standard form.
//Computes a ^ b, and outputs it in boolean standard form.
template XOR() {
    signal input a;
    signal input b;
    signal output out <== a + b - 2 * a * b;
}

// Does not assume that a and b are in boolean standard form.
// Computes a && b, and outputs it in boolean standard form.
template SafeAND() {
    signal input a;
    signal input b;
    component c1 = IsNotZero();
    component c2 = IsNotZero();
    c1.in <== a;
    c2.in <== b;
    signal std_a <== c1.is_not_zero;
    signal std_b <== c2.is_not_zero;

    signal output out <== std_a * std_b;
}

// Does not assume that a and b are in boolean standard form.
//Computes a || b, and outputs it in boolean standard form.
template SafeOR() {
    signal input a;
    signal input b;

    component c1 = IsNotZero();
    component c2 = IsNotZero();
    c1.in <== a;
    c2.in <== b;
    signal std_a <== c1.is_not_zero;
    signal std_b <== c2.is_not_zero;

    signal out <== std_a + std_b - std_a * std_b;
}

// Does not assume that a and b are in boolean standard form.
//Computes a ^ b, and outputs it in boolean standard form.
template SafeXOR() {
    signal input a;
    signal input b;

    component c1 = IsNotZero();
    component c2 = IsNotZero();
    c1.in <== a;
    c2.in <== b;
    signal std_a <== c1.is_not_zero;
    signal std_b <== c2.is_not_zero;

    signal output out <== std_a + std_b - 2 * std_a * std_b;
}

// Given a N long array input `in` with entries in boolean standard form,
// the output is `out = in[0] && ... && in[N - 1]`
template SEQUENCE_AND(N) {
    assert(N > 0);
    signal input in[N];
    signal output out;

    if (N == 1) {
        out <== in[0];
    } else {
        component recursive_and = SEQUENCE_AND(N - 1);
        for(var i = 0; i < N - 1; i++) {
            recursive_and.in[i] <== in[i];
        }
        out <== in[N - 1] * recursive_and.out;
    }
}

// Given a N long array input `in` with entries in boolean standard form,
// the output is `out = in[0] || ... || in[N - 1]`
template SEQUENCE_OR(N) {
    assert(N > 0);
    signal input in[N];
    signal output out;

    if (N == 1) {
        out <== in[0];
    } else {
        component recursive_or = SEQUENCE_OR(N - 1);
        for(var i = 0; i < N - 1; i++) {
            recursive_or.in[i] <== in[i];
        }
        // OR(a, b) == NOT( AND(NOT(a), NOT(b)) )
        out <== 1 - (1 - in[N - 1]) * (1 - recursive_or.out);
    }
}



//Ok cool, we managed to write bool expressions and equality tests, big achievement.
// What about other very complex relations, like a < b?
// Well, since every variable is just some remainder class modulo some prime p,
// the concept of "<" kinda loses sense in this setting.
// As a consequence, we have to emulate it to the best of our capabilities.
// What does it mean?
// It turns out, we cannot simulate it in full, but we can choose some constant M, and test the relation
// (a % M) < (b % M).
//
// First we need some helper functionality:

//Given `in`, if `in < 2 ** n`, then the output is `bits`,
// a n-long vector with all entries set to either 0 or 1, such that
// `in == sum(bit * 2 ** i for (bit, i) in enumerate(bits))`.
// Raises an error if `in >= 2 ** n`
template NumberToBits(n) {
    signal input in;
    signal output bits[n];

    // We declare an auxiliary array of numbers.
    // It will satisfy the property that, for every j,
    // bit_sums[j] = sum( bits[k] * 2 ** k for k in [0..j] )
    //
    // As a consequence, it should hold that bit_sums[n + 1] == in.
    signal bit_sums[n+1];
    bit_sums[0] <== 0;

    // We incrementally compute, and proof-check, the entries of bits, and of bit_sums.
    for(var i = 0; i < n; i++) {
        // Standard way to isolate the i-th bit of the binary representation of a number.
        bits[i] <-- (in & (1 << i)) >> i;
        // We force the bit to be 0 or 1, so that a malicious prover cannot insert an invalid binary digit.
        bits[i] * (bits[i] - 1) === 0;

        // We compute the next entry of bit_sums, and we proof-check that it is what it should be.
        bit_sums[i + 1] <== (bit_sums[i] + bits[i] * (1 << i));
    }
    //We make the final check, that (indirectly) forces the `bits` output to be the correct one,
    // i.e. we check that bit_sums[n] === in.
    // Since that check is not of the form A * B === C, we have to get creative.
    //
    // We could use the IsEqual template, but since in this case we are also asserting the result of the comparison,
    // it is more efficient to just exploit that 0 is the only solution to x * x === 0.
    (bit_sums[n] - in) * (bit_sums[n] - in) === 0;
    // Uncomment this comment block to enable debug output.
    /*
    log("The binary expansion of the number ", in, "is ");
    for(var i = 0; i < n; i++) {
        log(bits[i]);
    }
    */
}

template ReverseArray(n) {
    signal input in[n];
    signal output out[n];
    for (var i = 0; i < n; i++) {
        out[i] <== in[n - i - 1];
    }
}

//Compares the numbers a and b, and outputs
// -1 if a <  b
//  0 if a == b
//  1 if a >  b
//This function raises an error if (a >= 2 ** n) || (b >= 2 ** n)
template Compare(n) {
    signal input a;
    signal input b;

    // We compute the binary representations of a and b, and then we reverse their order so that
    // the most significant digits are first.
    component c1 = NumberToBits(n);
    component c2 = NumberToBits(n);
    component c3 = ReverseArray(n);
    component c4 = ReverseArray(n);
    c1.in <== a;
    c2.in <== b;
    c3.in <== c1.bits;
    c4.in <== c2.bits;
    signal a_bits[n] <== c3.out;
    signal b_bits[n] <== c4.out;
    //Now we have the digits, and what we will do is the following:
    // we start comparing the most significant digits,
    //    - if they are equal, we discard the digits, and compare the next most significant digits
    //    - if they are not equal, we set the output to 1 or -1 depending on which is bigger
    //    - if we consume all the arrays and all comparisons returned equality, we set the output to 0
    //
    // Of course, since all the signals are immutable and are computed without any flow control,
    // it follows that the above algorithm has to be adapted.

    // This array records, at every position j, the result of the comparison among
    // the j most significant digits of a and b.
    // The same as the output, every value in this array is either -1, 0, or 1
    signal partial_comparisons[n + 1];
    // When we compare "the 0 most significant digits", we are not comparing anything,
    // so this value is set to 0.
    partial_comparisons[0] <== 0;

    // This array only exists because of the "A * B === C" constraint on the expressions for the === operator.
    // It basically satisfies the following relation:
    // auxiliary_values[j] == 1 - partial_comparisons[j] ** 2
    signal auxiliary_values[n];
    
    for(var i = 0; i < n; i++) {
        // If partial_comparisons[i] is not 0, we just copy the value over the i+1 entry.
        // Otherwise, we compare the i-th most significant bits of a and b.
        partial_comparisons[i + 1] <--
            (partial_comparisons[i] == 0) ?
            a_bits[i] - b_bits[i] :  partial_comparisons[i];
        
        // This is equivalent to applying IsZero to partial_comparisons[i],
        // but since we have additional information on its value (-1, 0, or 1),
        // we can be smart about it and save computation.
        auxiliary_values[i] <== 1 - partial_comparisons[i] * partial_comparisons[i];

        // If partial_comparisons[i] == 0, equivalently if auxiliary_values[i] == 1,
        // we impose that
        // partial_comparisons[i + 1] == a_bits[i] - bits[i]
        (partial_comparisons[i + 1] - a_bits[i] + b_bits[i]) * auxiliary_values[i] === 0;

        // If partial_comparisons[i] != 0, then we impose that
        // partial_comparisons[i + 1] == partial_comparisons[i]
        (partial_comparisons[i + 1] - partial_comparisons[i]) * partial_comparisons[i] === 0;
    }
    signal output out <== partial_comparisons[n];
    //log("The result of the comparison between ", a, " and ", b, " is ", out);
}

// Outputs a < b in boolean standard form.
// If a >= 2 ** n || b >= 2 ** n the function throws an error
template LessThan(n) {
    signal input a;
    signal input b;
    component c = Compare(n);
    c.a <== a;
    c.b <== b;
    signal output out <-- (c.out == -1) ? 1 : 0;
    // Knowing that c.out is either -1, 0, 1, we impose that
    // if c.out == -1, then out == 1
    // if c.out == 0, then out == 0
    // if c.out == 1, then out == 0
    2 * out === c.out * (c.out - 1);
}

// Outputs a <= b in boolean standard form.
// If a >= 2 ** n || b >= 2 ** n the function throws an error
template LessOrEqualThan(n) {
    signal input a;
    signal input b;
    component c = Compare(n);
    c.a <== a;
    c.b <== b;
    signal output out <-- (c.out == -1 || c.out == 0) ? 1 : 0;
    // Knowing that c.out is either -1, 0, 1, we impose that
    // if c.out == -1, then out == 1
    // if c.out == 0, then out == 1
    // if c.out == 1, then out == 0
    2 * out === (1 - c.out) * (2 + c.out);
}

// The other comparison functions (GreaterThan, GreaterOrEqualThan) are derived analogously.

// One could also want to compute the function that compares the input with a given constant, and not with another signal.
// This is the case for the sudoku checker that we are going to implement.
// Implementing a function explicitly for that task allows us to program a more efficient circuit.
// This example is also useful to get a sense of what compile-time computations circom can perform.
// 
// Let's then implement this simplified comparison function:

// Compares in with N, outputs -1 if in < N, 0 if in == N, 1 if in > N
template CompareWithConstant(N, BitsOfInput) {
    // BitsOfInput acts like the "n" parameter in the Compare template.
    // We have to make sure that 2 ** BitsOfInput >= N.

    
    var power_of_2 = 1;
    var power_of_2_bigger_than_N = 0;
    var power_of_2_wraps_around = 0;
    for(var i = 0; i < BitsOfInput; i++) {
        // If power_of_2_wraps_around != 0, and the for loop does not end, that means that
        // 2 ** BitsOfInput > 2 * p, where p is the global prime that circom uses.
        // As this would produce undefined behavior, we don't allow it.
        assert(power_of_2_wraps_around == 0);
        var tmp = power_of_2 * 2;
        if (tmp < power_of_2) {
            power_of_2_wraps_around = 1;
        } else {
            power_of_2 = tmp;
            if (power_of_2 >= N) {
                power_of_2_bigger_than_N = 1;
            }
        }
    }
    // Assert that either the comparison power_of_2 >= N succeeded at least once,
    // or that, if p is the global very big prime number that circom uses, one has
    // 2 ** BitsOfInput > p > 2 ** (BitsOfInput - 1)
    
    assert(power_of_2_bigger_than_N || power_of_2_wraps_around);

    signal input in;
    signal output out;

    // As in the Compare template, we compute the binary representation of in,
    // and we order it from most to least significant digit
    component compute_input_binary = NumberToBits(BitsOfInput);
    compute_input_binary.in <== in;
    component reverse_input_binary = ReverseArray(BitsOfInput);
    reverse_input_binary.in <== compute_input_binary.bits;
    signal in_bits[BitsOfInput] <== reverse_input_binary.out;

    // This array has the same exact role of the omonimous array in the Compare template.
    signal partial_comparisons[BitsOfInput + 1];
    partial_comparisons[0] <== 0;

    // This array also has the same role as in Compare. It satisfies the relation
    // auxiliary_values[j] == (partial_comparisons[j + 1] == 0)
    signal auxiliary_values[BitsOfInput];
    
    for (var i = 0; i < BitsOfInput; i++) {
        var j = BitsOfInput - i - 1;
        // As in the Compare template, we compare the i most significant digits,
        // but in this case, we can know at compile time the digits of N.
        partial_comparisons[i + 1] <--
            (partial_comparisons[i] != 0) ?
                partial_comparisons[i] :
                in_bits[i] - ((N & (1 << j)) >> j);
        
        auxiliary_values[i] <== 1 - partial_comparisons[i] * partial_comparisons[i];

        // If partial_comparisons[i] != 0, then we enforce that
        // partial_comparisons[i + 1] == partial_comparisons[i]
        (partial_comparisons[i + 1] - partial_comparisons[i])
            * partial_comparisons[i] === 0;

        // If partial_comparisons[i] == 0,
        // i.e. if auxiliary_values[i] != 0, then we enforce that
        // partial_comparisons[i + 1] == ((in & (1 << j)) >> j) - ((N & (1 << j)) >> j)
        (partial_comparisons[i + 1] - in_bits[i] + ((N & (1 << j)) >> j))
            * auxiliary_values[i] === 0;
    }

    out <== partial_comparisons[BitsOfInput];
    //log("Comparing ", in, " with the constant ", N, " the result is ", out);
}

// Excellent! Now we have seen enough toy examples of circom templates,
// and we will be able to program non-trivial things,
// like for example proving that a sudoku has a solution, without showing it!

// The basic requirement of every sudoku is that
// some groups of 9 cells contain a permutation of the numbers from 1 to 9
// Let's make a circuit that allows us to check that a vector of inputs satisfies this property.

/*
The smart way to do that would have O(N) complexity,
and would roughly be like
signal input in[N]
signal aux[N]
for(var i = 0; i < N; i++) {
    aux[i] = 0;
}
var var_out = 1;
for(var i = 0; i < N; i++) {
    if (aux[in[i]] == 0) {
        aux[in[i]] = 1;
    } else {
        var_out = 0;
    }
}
signal output out <-- out;

but this approach has a problem:
it is eiether very hard or impossible to check its consistency in o(N^2)
using the === operator.

Another possibly viable approach would be sorting the array and checking
if the output is the array [1, 2, ..., N]
however i also spent roughly one day trying to find ordering algorithms
that can be checked with === in o(N^2), but i could not find any

So we have one practical observation:
Even if it is possible to check everything that can be written in a program,
programs with a lot of "if" statements can probably
only be proved with an asymptotic cost that is worse than the execution time.
*/

// Checks that the array contains all numbers from 1 to N without duplicates.
// Ugly O(N*N) circuit size. Can we do better?
template ArrayIsPermutationOf1To(N) {
    signal input in[N];

    // We check, for every i, for every j, if in[0..j] contains the number i.
    // If all numbers from 1 to N are present in an N long array,
    // then the array cannot contain duplicates.
    component i_is_equal_to_in_j[N][N];
    component some_entry_equal_to_i[N];
    component all_required_numbers_are_there = SEQUENCE_AND(N);

    for (var i = 0; i < N; i++) {

        some_entry_equal_to_i[i] = SEQUENCE_OR(N);

        for (var j = 0; j < N; j++) {
            i_is_equal_to_in_j[i][j] = IsEqual();
            i_is_equal_to_in_j[i][j].a <== i + 1;
            i_is_equal_to_in_j[i][j].b <== in[j];
            // We set one of the inputs. If at least one of those is 1,
            // then we know that in[j] == i, for some j.
            some_entry_equal_to_i[i].in[j] <== i_is_equal_to_in_j[i][j].out;
        }
        
        all_required_numbers_are_there.in[i] <== some_entry_equal_to_i[i].out;
    }
    signal output out <== all_required_numbers_are_there.out;
}

template IsValidSudoku(N) {
    var size = N * N;
    signal input grid[size][size];
    component valid_row_circuits[size];
    component valid_column_circuits[size];
    component valid_region_circuits[size];

    for (var i = 0; i < size; i++) {
        valid_row_circuits[i]    = ArrayIsPermutationOf1To(size);
        valid_column_circuits[i] = ArrayIsPermutationOf1To(size);
        valid_region_circuits[i] = ArrayIsPermutationOf1To(size);
    }

    // every row, column, and region, has an associated check.
    // These signals check if the tests were successful.
    // Every time we perform a new check, we have to report its result here.
    component checks_passed = SEQUENCE_AND(3 * size);

    for (var i = 0; i < size; i++) {
        valid_row_circuits[i].in <== grid[i];
        checks_passed.in[i] <== valid_row_circuits[i].out;
    }
    for (var i = 0; i < size; i++) {
        for(var j = 0; j < size; j++) {
            valid_column_circuits[i].in[j] <== grid[j][i];
        }
        checks_passed.in[size + i] <== valid_column_circuits[i].out;
    }
    // For the regions we have to do some more index manipulations in order
    // to feed the correct data to the "ArrayIsPermutationOf1To" component.
    // Sorry for this punch in the eyes :)
    for (
        var region_row_coord = 0;
        region_row_coord < N;
        region_row_coord++
    ) {
        for (
            var region_column_coord = 0;
            region_column_coord < N;
            region_column_coord++
        ) {
            var region_number = N * region_row_coord + region_column_coord;
            for(
                var j_row = 0;
                j_row < N;
                j_row++
            ) {
                for(
                    var j_column = 0;
                    j_column < N;
                    j_column++
                ) {
                    valid_region_circuits[region_number]
                        .in[N * j_row + j_column]
                        <== grid[
                            N * region_row_coord + j_row
                        ][
                            N * region_column_coord + j_column
                        ];
                }
            }

            checks_passed.in[2 * size + region_number]
            <== valid_region_circuits[region_number].out;
        }
    }
    signal output out <== checks_passed.out;
}

template AssertValidSudokuSolution(N) {
    var size = N * N;
    signal input problem[size][size];
    signal input solution[size][size];
    // First we check that the solution is a valid sudoku.
    component check_valid_solution = IsValidSudoku(N);
    check_valid_solution.grid <== solution;
    // Then, we check that the problem consists of a grid with cells that
    // are either 0, or such that they coincide with
    // the cell in the same index in the solution.
    for(var i = 0; i < size; i++) {
        for(var j = 0; j < size; j++) {
            // We impose that either problem[i][j] == 0,
            // or that problem[i][j] == solution[i][j]
            problem[i][j] * (problem[i][j] - solution[i][j]) === 0;
        }
    }
    signal output out <== check_valid_solution.out;
    out === 1;
}

component main {public [problem]} = AssertValidSudokuSolution(3);