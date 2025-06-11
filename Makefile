IBEX_CONFIG ?= small

FUSESOC_CONFIG_OPTS = $(shell ./util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)

all: help

.PHONY: help
help:
	@echo "This is a short hand for running popular tasks."
	@echo "Please check the documentation on how to get started"
	@echo "or how to set-up the different environments."

# Use a parallel run (make -j N) for a faster build
build-all: build-riscv-compliance build-simple-system build-arty-100 \
      build-csr-test


# RISC-V compliance
.PHONY: build-riscv-compliance
build-riscv-compliance:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_riscv_compliance \
		$(FUSESOC_CONFIG_OPTS)

# Simple system
# Use the following targets:
# - "build-simple-system"
# - "run-simple-system"
.PHONY: build-simple-system
build-simple-system:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_simple_system \
		$(FUSESOC_CONFIG_OPTS)

build-multicore-system:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_multicore_system \
		$(util/ibex_config.py small fusesoc_opts)

simple-system-program = examples/sw/simple_system/hello_test/hello_test.vmem
sw-simple-hello: $(simple-system-program)

.PHONY: $(simple-system-program)
$(simple-system-program):
	cd examples/sw/simple_system/hello_test && $(MAKE)

Vibex_simple_system = \
      build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system
$(Vibex_simple_system):
	@echo "$@ not found"
	@echo "Run \"make build-simple-system\" to create the dependency"
	@false

run-simple-system: sw-simple-hello | $(Vibex_simple_system)
	build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system \
		--raminit=$(simple-system-program)


# Arty A7 FPGA example
# Use the following targets (depending on your hardware):
# - "build-arty-35"
# - "build-arty-100"
# - "program-arty"
arty-sw-program = examples/sw/led/led.vmem
sw-led: $(arty-sw-program)

.PHONY: $(arty-sw-program)
$(arty-sw-program):
	cd examples/sw/led && $(MAKE)

.PHONY: build-arty-35
build-arty-35: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7 --part xc7a35ticsg324-1L

.PHONY: build-arty-100
build-arty-100: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1

.PHONY: program-arty
program-arty:
	fusesoc --cores-root=. run --target=synth --run \
		lowrisc:ibex:top_artya7


# Lint check
.PHONY: lint-core-tracing
lint-core-tracing:
	fusesoc --cores-root . run --target=lint lowrisc:ibex:ibex_core_tracing \
		$(FUSESOC_CONFIG_OPTS)


# CS Registers testbench
# Use the following targets:
# - "build-csr-test"
# - "run-csr-test"
.PHONY: build-csr-test
build-csr-test:
	fusesoc --cores-root=. run --target=sim --setup --build \
	      --tool=verilator lowrisc:ibex:tb_cs_registers
Vtb_cs_registers = \
      build/lowrisc_ibex_tb_cs_registers_0/sim-verilator/Vtb_cs_registers
$(Vtb_cs_registers):
	@echo "$@ not found"
	@echo "Run \"make build-csr-test\" to create the dependency"
	@false

.PHONY: run-csr-test
run-csr-test: | $(Vtb_cs_registers)
	fusesoc --cores-root=. run --target=sim --run \
	      --tool=verilator lowrisc:ibex:tb_cs_registers

# Echo the parameters passed to fusesoc for the chosen IBEX_CONFIG
.PHONY: test-cfg
test-cfg:
	@echo $(FUSESOC_CONFIG_OPTS)

.PHONY: python-lint
python-lint:
	$(MAKE) -C util lint

.PHONY: run_hello_test repeat_hello_test

build_ram:
	./gen_multicore_system_main.py $(NUM_RAMS) ./examples/multicore_system/ibex_multicore_system_main.cc
	./gen_multicore_system_header.py $(NUM_RAMS) ./examples/multicore_system/ibex_multicore_system.h
	./gen_multicore_system.py $(NUM_RAMS) ./examples/multicore_system/ibex_multicore_system.cc
	make build_cores NUMRAMS=$(NUM_RAMS)
	make build-multicore-system


run_sim:
	@set -e ; \
	ARGS="" ; \
	for i in $$(seq 1 $(NUM_RAMS)); do \
		core_idx=$$(( i - 1 )); \
		ARGS="$$ARGS --meminit=ram$$i,./examples/sw/simple_system/hello_test/core$${core_idx}.elf" ; \
	done ; \
	echo "Running with: $$ARGS" ; \
	exec ./build/lowrisc_ibex_ibex_multicore_system_0/sim-verilator/Vibex_multicore_system -t $$ARGS

do_sim:
	make build_ram NUM_RAMS=$(NUM_RAMS)
	make run_sim NUM_RAMS=$(NUM_RAMS)

build_cores:
	@set -e ; \
	for i in $$(seq 0 $$(( $(NUM_RAMS) - 1 ))); do \
		n=$$(( i + 1 )); \
		./gen_ld.py $$n ./examples/sw/simple_system/common/link.ld ; \
		$(MAKE) -C examples/sw/simple_system/hello_test ; \
		mv ./examples/sw/simple_system/hello_test/hello_test.elf \
		   ./examples/sw/simple_system/hello_test/core$$i.elf ; \
	done


run_hello_test:
	python3 examples/sw/simple_system/hello_test/csrmatrix.py
	python3 examples/sw/simple_system/hello_test/changecfile.py
	make -C examples/sw/simple_system/hello_test
	./build/lowrisc_ibex_ibex_multicore_system_0/sim-verilator/Vibex_multicore_system -t --meminit=ram,./examples/sw/simple_system/hello_test/hello_test.elf
	python3 examples/sw/simple_system/hello_test/checkresults.py

run_hello_test_2:
	python3 examples/sw/simple_system/hello_test/changecfile.py
	make -C examples/sw/simple_system/hello_test
	./build/lowrisc_ibex_ibex_multicore_system_0/sim-verilator/Vibex_multicore_system -t --meminit=ram,./examples/sw/simple_system/hello_test/hello_test.elf
	python3 examples/sw/simple_system/hello_test/checkresults.py

repeat_hello_test:
	@count=0; \
	while [ $$count -lt $(NUM_RUNS) ]; do \
		echo "Run $$count..."; \
		$(MAKE) run_hello_test; \
		count=`expr $$count + 1`; \
	done
