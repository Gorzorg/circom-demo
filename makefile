name := sudoku_proof_of_solution

r1cs := $(name).r1cs
wasm := $(name)_js/$(name).wasm
witness_generator := $(name)_js/generate_witness.js

compile_outputs := node $(name)_js/witness_calculator.js $(r1cs) $(wasm) $(witness_generator)

circom = $(name).circom
pk = $(name).pk
vk = $(name).vk
ptau = $(name).ptau
keys = $(pk) $(vk)
p_input = input.json
wit = $(name).wtns

pf = $(name).pf.json
inst = $(name).inst.json
prove_outputs = $(pf) $(inst)


all: verify

$(compile_outputs): $(circom)
	circom $< --r1cs --wasm

$(ptau):
	snarkjs powersoftau new bn128 14 tmp.ptau
	snarkjs powersoftau prepare phase2 tmp.ptau $(ptau)
	rm tmp.ptau

$(keys): $(ptau) $(r1cs)
	snarkjs groth16 setup $(r1cs) $(ptau) $(pk)
	snarkjs zkey export verificationkey $(pk) $(vk)

$(wit): $(p_input) $(wasm) $(witness_generator)
	node $(witness_generator) $(wasm) $(p_input) $@

$(prove_outputs): $(wit) $(pk)
	snarkjs groth16 prove $(pk) $(wit) $(pf) $(inst)

.PHONY = verify clean

verify: $(pf) $(inst) $(vk)
	snarkjs groth16 verify $(vk) $(inst) $(pf)

clean:
	rm -f $(compile_outputs) $(ptau) $(keys) $(wit) $(prove_outputs)
	rmdir $(name)_js
