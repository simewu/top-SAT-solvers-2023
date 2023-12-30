#include "test.h"

#include "../src/application.h"
#include "../src/file.h"

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static char *copy_string(const char *begin, const char *end)
{
    const size_t len = end - begin;
    char *res = malloc(len + 1);
    memcpy(res, begin, len);
    res[len] = 0;
    return res;
}
char proof_out[] = "proof.out";
void tissat_call_application(int expected, const char *cmd)
{
#define MAX_ARGC 8
    char *argv[MAX_ARGC];
    int argc = 0;
    argc = 1;
    argv[0] = "X";
    for (const char *p = cmd, *start = cmd;; p++)
        if (!*p || *p == ' ') {
            if (argc == MAX_ARGC)
                FATAL("MAX_ARGC exceeded");
            argv[argc++] = copy_string(start, p);
            if (!*p)
                break;
            start = ++p;
        }
    //if(check_proof) {
    bool proving = true;
    bool binary = true;
    bool check_solution = false;
    argv[argc++] = malloc(15);//copy_string(proof_out, proof_out + 9);
    strcpy(argv[argc - 1], "--timeout=5000");
    if(proving) {//default: pseudo boolean format.
        if(binary) {
            argv[argc++] = malloc(14);//copy_string(proof_out, proof_out + 9);
            strcpy(argv[argc - 1], "--binary=true");
            argv[argc++] = malloc(17);//copy_string(proof_out, proof_out + 9);
            strcpy(argv[argc - 1], "--symmetry=true");
            argv[argc++] = malloc(17);//copy_string(proof_out, proof_out + 9);
            strcpy(argv[argc - 1], "--walkstrategy=0");
        }
        if(argv[1][15] % 2) {
            argv[argc++] = malloc(3 + strlen(argv[1]) + 1 + 6);//copy_string(proof_out, proof_out + 9);
            memcpy(argv[argc - 1] + 3, argv[1], strlen(argv[1]));
            strcpy(argv[argc - 1] + 3 + strlen(argv[1]), ".proof");
            memcpy(argv[argc - 1], "/home/a/vdb", 11);
        }else {
            argv[argc++] = malloc(strlen(argv[1]) + 1 + 6);//copy_string(proof_out, proof_out + 9);
            memcpy(argv[argc - 1], argv[1], strlen(argv[1]));
            strcpy(argv[argc - 1] + strlen(argv[1]), ".proof");
        }
    }
    //}
#undef MAX_ARGC
    bool check_proof = true;
    if(check_proof == true && proving == false) {
        FATAL("cannot check proof without proving");
    }
    kissat *solver = kissat_init(0);
    tissat_init_solver(solver);
    tissat_redirect_stderr_to_stdout();
    //printf("aaa");
    char * solution_file = NULL;
    char * solution_file_pure = NULL;
    if(check_solution) {
        solution_file = malloc(strlen(argv[1]) + 1 + 4);
        memcpy(solution_file, argv[1], strlen(argv[1]));
        strcpy(solution_file + strlen(argv[1]), ".sol");
        solution_file_pure = malloc(strlen(argv[1]) + 1 + 4);
        memcpy(solution_file_pure, argv[1], strlen(argv[1]));
        strcpy(solution_file_pure + strlen(argv[1]), ".sat");
        freopen(solution_file, "w", stdout);
    }
    int res = kissat_application(solver, argc, argv);
    if(res == 40) {
        tissat_restore_stderr();
        kissat_release(solver);
        solver = kissat_init(40);
        tissat_redirect_stderr_to_stdout();
        res = kissat_application(solver, argc, argv);
    }
    //printf("aaa");
    tissat_restore_stderr();
    static char cc[999];
    if(check_solution && res == 10) {
        fclose(stdout);
        freopen("/dev/tty", "w", stdout);
        sprintf(cc, "sed -re '/^v/!d;s/^v//' %s > %s", solution_file, solution_file_pure);
        system(cc);
        sprintf(cc, "gratchk sat %s %s", argv[1], solution_file_pure);
        if(!system(cc)){
		printf("%s\n", cc);
		fflush(stdout);
        }else{
            FATAL("solution check failed. kissat %s returned correct result %d with wrong solution.", cmd, res);
        }
        sprintf(cc, "rm %s", solution_file);
        system(cc);
        
        sprintf(cc, "rm %s", solution_file_pure);
        system(cc);
    }
    if (res != expected) {
        if(expected == 30 || res == 30) {
        }else {
            FATAL("'kissat %s' returns '%d' and not '%d' (%s)", cmd, res, expected, argv[argc - 1]);
        }
    }
    kissat_release(solver);
    tissat_verbose("Application 'kissat %s' returned '%d' as expected.", cmd, res);
    
    
    if(check_proof && res != 30) {
        if(binary) {
            if(res == 20) {
                int sta;
                sprintf(cc, "./../../../dpr-trim-master/dpr-trim %s %s", argv[1], argv[argc - 1]);
                sta = system(cc);
                
                if(sta != 0) {
                    FATAL("proof check failed. kissat %s returned correct result %d with wrong certificate.", cmd, res);
                }else {
                    fprintf(stderr, "proof checked\n");
                    
                }
            }
        }else {
            if(res == 20) {
                int sta;
                sprintf(cc, "veripb --cnf %s %s", argv[1], argv[argc - 1]);
                sta = system(cc);
                
                
                if(sta != 0) {
                    FATAL("proof check failed. kissat %s returned correct result %d with wrong certificate.", cmd, res);
                }else {
                //    printf("proof checked\n");
                }
            }
        }
    }
    if(proving) {
        sprintf(cc, "rm %s", argv[argc - 1]);
        system(cc);
    }
    for (int i = 1; i < argc; i++)
        free(argv[i]);
}

const char *tissat_options[] = {
    "",
#if !defined(QUIET) && !defined(NOPTIONS)
    "-q ",
    "-s ",
    "-v ",
    "-s -v ",
#endif
};

#define SIZE_OPTIONS (sizeof(tissat_options) / sizeof(char *))
const unsigned tissat_size_options = SIZE_OPTIONS;
const char **tissat_end_of_options = tissat_options + SIZE_OPTIONS;

const char *tissat_next_option(unsigned count)
{
    assert(tissat_size_options);
    return tissat_options[count % tissat_size_options];
}
