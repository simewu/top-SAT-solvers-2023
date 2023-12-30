#include "test.h"

#include "../src/file.h"

char sc[444][999] = {
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_3_3",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_4_4",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_5_5",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_6_6",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_7_7",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_8_8",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_9_9",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_10_10",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_11_11",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_12_12",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_13_13",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_14_14",
"../test/0707/outgoing-_-Mult_op-_-mult_op_DEMO1_15_15",
};

void
tissat_schedule_chip (void)
{
#define APP tissat_schedule_application
    for(int i = 3; i <=15; i++) {
        for(int j = 1; j <= i * 2; j++) {
            char tmp[999];
            sprintf(tmp, "%s/TOP%d_cnf.txt", sc[i - 3], j);
            APP ((30), tmp);
            /*sprintf(tmp, "%s/TOP%d_cnf.txt --mablrb=0", sc[i - 3], j);
            APP ((30), tmp);
            sprintf(tmp, "%s/TOP%d_cnf.txt --mabchb=0", sc[i - 3], j);
            APP ((30), tmp);
            sprintf(tmp, "%s/TOP%d_cnf.txt --mabvsids=0", sc[i - 3], j);
            APP ((30), tmp);
            sprintf(tmp, "%s/TOP%d_cnf.txt --mablrb=0 --mabvsids=0", sc[i - 3], j);
            APP ((30), tmp);
            sprintf(tmp, "%s/TOP%d_cnf.txt --mablrb=0 --mabchb=0", sc[i - 3], j);
            APP ((30), tmp);
            sprintf(tmp, "%s/TOP%d_cnf.txt --mabchb=0 --mabvsids=0", sc[i - 3], j);
            APP ((30), tmp);*/
        }
    }

#undef APP
}
