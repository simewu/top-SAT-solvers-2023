all:
	$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build"
kissat:
	$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build" kissat
tissat:
	$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build" tissat
clean:
	rm -f "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources"/makefile
	-$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build" clean
	rm -rf "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build"
coverage:
	$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build" coverage
indent:
	$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build" indent
test:
	$(MAKE) -C "/media/sf_Shared/top-SAT-solvers-2023/2_kissat_mab_prop/sources/build" test
.PHONY: all clean coverage indent kissat test tissat
