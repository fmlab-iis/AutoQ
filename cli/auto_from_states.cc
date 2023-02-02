#include <autoq/util/aut_description.hh>

using namespace std;
using AUTOQ::Util::TreeAutomata;

int main(int argc, char **argv) {
    TreeAutomata aut;
    for (int z=1; z<argc; z++) {
        TreeAutomata aut2;
        int cnt = 0;
        while (true) {
            char ch = argv[z][cnt++];
            if (ch == '0') {
                if (cnt > 1)
                    aut2.transitions[cnt][{2*cnt-1, 2*cnt-1}] = {2*(cnt-1)-1};
                aut2.transitions[cnt][{2*cnt, 2*cnt-1}] = {2*(cnt-1)};
            }
            else if (ch == '1') {
                if (cnt > 1)
                    aut2.transitions[cnt][{2*cnt-1, 2*cnt-1}] = {2*(cnt-1)-1};
                aut2.transitions[cnt][{2*cnt-1, 2*cnt}] = {2*(cnt-1)};
            }
            else {
                cnt--;
                aut2.transitions[{0,0,0,0,0}][{}] = {2*cnt-1};
                aut2.transitions[{1,0,0,0,0}][{}] = {2*cnt};
                aut2.finalStates = {0};
                aut2.stateNum = 2 * cnt;
                aut2.qubitNum = cnt;
                break;
            }
        }
        aut = aut.Union(aut2);
    }
    aut.fraction_simplification();
    aut.reduce();
    aut.print();
    return 0;
}