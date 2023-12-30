#ifndef NPROOFS

#include "allocate.h"
#include "file.h"
#include "inline.h"
#include "simplify.h"

void kissat_init_proof(kissat *solver, file *file, bool binary)
{
    assert(file);
    assert(!solver->proof);
    proof *proof = kissat_calloc(solver, 1, sizeof(struct proof));
    proof->binary = binary;
    proof->file = file;
    solver->proof = proof;
    if (!proof->binary) {
        kissat_puts(proof->file, "pseudo-Boolean proof version 2.0\n");
    }
    LOG("starting to trace %s proof", binary ? "binary" : "non-binary");
}

void kissat_release_proof(kissat *solver, int res)
{
    proof *proof = solver->proof;
    assert(proof);
    if (!proof->binary) {
        kissat_puts(proof->file, "output NONE\nconclusion ");
        kissat_puts(proof->file, res ? "UNSAT" : "SAT");
        kissat_puts(proof->file, "\nend pseudo-Boolean proof\n");
    }
    file_flush_buffer(proof->file);
    LOG("stopping to trace proof");
    RELEASE_STACK(proof->line);
    kissat_free(solver, proof, sizeof(struct proof));
    solver->proof = 0;
}

#ifndef QUIET

#include <inttypes.h>

#define PERCENT_LINES(NAME) kissat_percent(proof->NAME, proof->lines)

void kissat_print_proof_statistics(kissat *solver, bool verbose)
{
    proof *proof = solver->proof;
    PRINT_STAT("proof_added", proof->added, PERCENT_LINES(added), "%", "per line");
    PRINT_STAT("proof_bytes", proof->file->bytes, proof->file->bytes / (double)(1 << 20), "MB", "");
    PRINT_STAT("proof_deleted", proof->deleted, PERCENT_LINES(deleted), "%", "per line");
    if (verbose)
        PRINT_STAT("proof_lines", proof->lines, 100, "%", "");
    if (verbose)
        PRINT_STAT("proof_literals", proof->literals, kissat_average(proof->literals, proof->lines), "", "per line");
}

#endif

static void import_internal_proof_literal(kissat *solver, proof *proof, unsigned ilit)
{
    int elit = kissat_export_literal(solver, ilit);
    int real_idx = solver->mapidx[abs(elit)];
    int real_lit = real_idx * (elit > 0 ? 1 : -1);
    assert(real_lit);
    PUSH_STACK(proof->line, real_lit);
    proof->literals++;
}

static void import_external_proof_literal(kissat *solver, proof *proof, int elit)
{
    assert(elit);
    int real_idx = solver->mapidx[abs(elit)];
    int real_lit = real_idx * (elit > 0 ? 1 : -1);

    PUSH_STACK(proof->line, real_lit);

    proof->literals++;
}

static void import_internal_proof_binary(kissat *solver, proof *proof, unsigned a, unsigned b)
{
    assert(EMPTY_STACK(proof->line));
    import_internal_proof_literal(solver, proof, a);
    import_internal_proof_literal(solver, proof, b);
}

static void import_internal_proof_literals(kissat *solver, proof *proof, size_t size, unsigned *ilits)
{
    assert(EMPTY_STACK(proof->line));
    assert(size <= UINT_MAX);
    for (size_t i = 0; i < size; i++) {
        import_internal_proof_literal(solver, proof, ilits[i]);
    }
}

static void import_external_proof_literals(kissat *solver, proof *proof, size_t size, int *elits)
{
    assert(EMPTY_STACK(proof->line));
    assert(size <= UINT_MAX);
    for (size_t i = 0; i < size; i++)
        import_external_proof_literal(solver, proof, elits[i]);
}

static void import_proof_clause(kissat *solver, proof *proof, clause *c)
{
    import_internal_proof_literals(solver, proof, c->size, c->lits);
}

static void print_binary_proof_line(proof *proof)
{
    assert(proof->binary);
    for (all_stack(int, elit, proof->line)) {
        
        unsigned x = 2u * ABS(elit) + (elit < 0);
        unsigned char ch;
        while (x & ~0x7f) {
            ch = (x & 0x7f) | 0x80;
            kissat_putc(proof->file, ch);
            x >>= 7;
        }
        kissat_putc(proof->file, (unsigned char)x);
    }
    kissat_putc(proof->file, 0);
}

static void print_non_binary_proof_line(proof *proof)
{
    assert(!proof->binary);
    // char buffer[16];
    // char *end_of_buffer = buffer + sizeof buffer;
    // *--end_of_buffer = 0;
    for (all_stack(int, elit, proof->line)) {
        //char *p = end_of_buffer;
        //assert(!*p);
        assert(elit);
        assert(elit != INT_MIN);
        kissat_puts(proof->file, " +1 ");
        if (elit < 0) {
            kissat_putc(proof->file, '~');
            elit *= -1;
        }
        kissat_putc(proof->file, 'x');

        kissat_putint(proof->file, elit);
    }
    kissat_puts(proof->file, " >= 1 ;\n");
}

static void print_proof_line(proof *proof)
{
    proof->lines++;
    if (proof->binary)
        print_binary_proof_line(proof);
    else
        print_non_binary_proof_line(proof);
    CLEAR_STACK(proof->line);
#ifndef NDEBUG
    fflush(proof->file->file);
#endif
}

void print_added_proof_line(proof *proof)
{
    proof->added++;
    if (proof->binary) {
        kissat_putc(proof->file, 'a');
    } else {
        kissat_puts(proof->file, "rup");
    }

    print_proof_line(proof);
}

void print_delete_proof_line(proof *proof)
{
    proof->deleted++;
    if (proof->binary) {
        kissat_putc(proof->file, 'd');
    } else {
        CLEAR_STACK(proof->line);
        return;
        kissat_puts(proof->file, "del spec");
    }

    print_proof_line(proof);
}

void kissat_add_binary_to_proof(kissat *solver, unsigned a, unsigned b)
{
    proof *proof = solver->proof;
    assert(proof);
    import_internal_proof_binary(solver, proof, a, b);
    print_added_proof_line(proof);
}

void kissat_add_clause_to_proof(kissat *solver, clause *c)
{
    proof *proof = solver->proof;
    assert(proof);
    import_proof_clause(solver, proof, c);
    print_added_proof_line(proof);
}

void kissat_add_empty_to_proof(kissat *solver)
{
    proof *proof = solver->proof;
    assert(proof);
    assert(EMPTY_STACK(proof->line));
    if (proof->binary) {
        print_added_proof_line(proof);
    } else {
        // do nothing in pseudo boolean mode
    }
}

void kissat_add_lits_to_proof(kissat *solver, size_t size, unsigned *ilits)
{
    proof *proof = solver->proof;
    assert(proof);
    import_internal_proof_literals(solver, proof, size, ilits);
    print_added_proof_line(proof);
}

void kissat_add_unit_to_proof(kissat *solver, unsigned ilit)
{
    proof *proof = solver->proof;
    assert(proof);
    assert(EMPTY_STACK(proof->line));
    import_internal_proof_literal(solver, proof, ilit);
    print_added_proof_line(proof);
}

void kissat_shrink_clause_in_proof(kissat *solver, clause *c, unsigned remove, unsigned keep)
{
    proof *proof = solver->proof;
    const value *values = solver->values;
    assert(EMPTY_STACK(proof->line));
    for (all_literals_in_clause(ilit, c)) {
        if (ilit == remove)
            continue;
        if (ilit != keep && values[ilit] < 0 && !LEVEL(ilit))
            continue;
        import_internal_proof_literal(solver, proof, ilit);
    }
    print_added_proof_line(proof);
    import_proof_clause(solver, proof, c);
    print_delete_proof_line(proof);
}

void kissat_delete_binary_from_proof(kissat *solver, unsigned a, unsigned b)
{
    proof *proof = solver->proof;
    assert(proof);
    import_internal_proof_binary(solver, proof, a, b);
    print_delete_proof_line(proof);
}

void kissat_delete_clause_from_proof(kissat *solver, clause *c)
{
    proof *proof = solver->proof;
    assert(proof);
    import_proof_clause(solver, proof, c);
    print_delete_proof_line(proof);
}

void kissat_delete_external_from_proof(kissat *solver, size_t size, int *elits)
{
    proof *proof = solver->proof;
    assert(proof);
    import_external_proof_literals(solver, proof, size, elits);
    print_delete_proof_line(proof);
    //CLEAR_STACK(proof->line);
}

void kissat_delete_internal_from_proof(kissat *solver, size_t size, unsigned *ilits)
{
    proof *proof = solver->proof;
    assert(proof);
    import_internal_proof_literals(solver, proof, size, ilits);
    print_delete_proof_line(proof);
}

void kissat_generate_preorder(kissat *solver, int nvars, int id)
{
    /* pre_order ternarylex
    vars
    left u1 u2 u3
    right v1 v2 v3
    aux
    end
    def
    -4 u1 4 v1 -2 u2 2 v2 -1 u3 1 v3 >= 0 ;
    end
    transitivity
    vars
    fresh_right w1 w2 w3
    end
    proof
    proofgoal #1
    pol 1 2 + 3 +
    end -1
    end
    end
    end */

    proof *proof = solver->proof;
    if (!proof)
        return;
    kissat_puts(proof->file, "pre_order order");
    kissat_putint(proof->file, id);
    kissat_puts(proof->file, "\n  vars\n    left");
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " u");
        kissat_putint(proof->file, i);
    }
    kissat_puts(proof->file, "\n    right");
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " v");
        kissat_putint(proof->file, i);
    }
    kissat_puts(proof->file, "\n    aux\n  end\n  def\n    ");
    for (int i = 1; i <= nvars; i++) {
        kissat_putint(proof->file, -1ll * (1ll << (nvars - i)));
        kissat_puts(proof->file, " u");
        kissat_putint(proof->file, i);
        kissat_putc(proof->file, ' ');
        kissat_putint(proof->file, 1ll * (1ll << (nvars - i)));
        kissat_puts(proof->file, " v");
        kissat_putint(proof->file, i);
        kissat_putc(proof->file, ' ');
    }
    kissat_puts(proof->file, ">= 0 ;\n  end\n  transitivity\n    vars\n      fresh_right");
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " w");
        kissat_putint(proof->file, i);
    }
    kissat_puts(proof->file,
        "\n    end\n    proof\n      proofgoal #1\n        pol -1 -2 + -3 +\n      end -1\n    end\n  end\nend\n");
}

/*void kissat_generate_preorder_with_aux(kissat *solver, int nvars) {
    proof *proof = solver->proof;
    if (!proof)
        return;
    kissat_puts(proof->file, "pre_order order");
    kissat_putint(proof->file, nvars);
    kissat_puts(proof->file, "\n  vars\n    left");
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " u");
        kissat_putint(proof->file, i);
    }
    for (int i = 0; i <= nvars; i++) {
        kissat_puts(proof->file, " a");
        kissat_putint(proof->file, i);
    }
    kissat_puts(proof->file, "\n    right");
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " v");
        kissat_putint(proof->file, i);
    }
for (int i = 0; i <= nvars; i++) {
        kissat_puts(proof->file, " b");
        kissat_putint(proof->file, i);
    }
    kissat_puts(proof->file, "\n    aux");
    
    kissat_puts(proof->file, "\n  end\n  def\n");
    kissat_puts(proof->file, "    1 a0 >= 1 ;\n");//1
    kissat_puts(proof->file, "    1 b0 >= 1 ;\n");//2
    for(int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, "    1 a");
        kissat_putint(proof->file, i - 1);
        kissat_puts(proof->file, " -1 u");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " 1 v");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " 1 a");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " >= -1 ;\n")//i + 2
    }
    kissat_puts(proof->file, "    -1 a");
    kissat_puts(proof->file, nvars);
    kissat_puts(proof->file, " >= -1 ;\n")//nvars + 3

    for(int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, "    1 a");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " 1 ~b");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " >= 1 ;");//nvars + 3 + 2 * i - 1
        kissat_puts(proof->file, "    1 b");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " 1 ~a");
        kissat_putint(proof->file, i);
        kissat_puts(proof->file, " >= 1 ;");//nvars + 3 + 2 * i
    }
    
    
    kissat_puts(proof->file, "  end\n  transitivity\n    vars\n      fresh_right");
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " w");
        kissat_putint(proof->file, i);
    }
    for (int i = 1; i <= nvars; i++) {
        kissat_puts(proof->file, " c");
        kissat_putint(proof->file, i);
    }
    kissat_puts(proof->file, "\n    end\n    proof\n      proofgoal #1\n");
    
        //        pol -1 -2 + -3 +\n      end -1\n    end\n  end\nend\n");
}*/
void kissat_derive_lex_order(kissat *solver, ints *support, int id)
{
    proof *proof = solver->proof;
    if (!proof)
        return;
    kissat_puts(proof->file, "load_order order");
    kissat_putint(proof->file, id);
    int nvars = SIZE_STACK(*support) / 2;
    for (int i = 0; i < nvars; i++) {
        int var = PEEK_STACK(*support, i * 2);
        kissat_puts(proof->file, " x");
        kissat_putint(proof->file, solver->mapidx[var + 1]);
    }
    kissat_puts(proof->file, "\n");


    kissat_puts(proof->file, "dom");
    for (int i = 0; i < nvars; i++) {
        int var = PEEK_STACK(*support, i * 2);
        kissat_putc(proof->file, ' ');
        kissat_putint(proof->file, 1ll << (nvars - i - 1));
        kissat_putc(proof->file, ' ');
        int mapped_to = PEEK_STACK(*support, i * 2 + 1);
        if (mapped_to % 2 == 1) {
            kissat_putc(proof->file, '~');
        }
        kissat_putc(proof->file, 'x');
        kissat_putint(proof->file, solver->mapidx[mapped_to / 2 + 1]);
        kissat_puts(proof->file, " -");
        kissat_putint(proof->file, 1ll << (nvars - i - 1));
        kissat_puts(proof->file, " x");
        kissat_putint(proof->file, solver->mapidx[var + 1]);
    }
    kissat_puts(proof->file, " >= 0 ;");
    for (int i = 0; i < nvars; i++) {
        int var = PEEK_STACK(*support, i * 2);
        kissat_puts(proof->file, " x");
        kissat_putint(proof->file, solver->mapidx[var + 1]);
        kissat_puts(proof->file, " -> ");
        int mapped_to = PEEK_STACK(*support, i * 2 + 1);
        if (mapped_to % 2 == 1) {
            kissat_putc(proof->file, '~');
        }
        kissat_puts(proof->file, "x");
        kissat_putint(proof->file, solver->mapidx[mapped_to / 2 + 1]);
    }
    kissat_puts(proof->file, " ; begin\nproofgoal #1\npol -1 -2 +\nend -1\nproofgoal #2\npol -1 -4 +\nend -1\nend");
    
    kissat_puts(proof->file, "\nload_order\n");
}

#else
int kissat_proof_dummy_to_avoid_warning;
#endif
