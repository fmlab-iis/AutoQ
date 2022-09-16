#include <fstream>
#include <iostream>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <iomanip>

using namespace std;
using VATA::Parsing::TimbukParser;
using VATA::Serialization::TimbukSerializer;
using VATA::Util::TreeAutomata;
using VATA::Util::ShellCmd;
using VATA::Util::ReadFile;

int type, n;

int rand_gen() {
    if (type == 3) return 1;
    else if (type == 5) return n;
    else return rand() % n + 1;
}

void rand_gen(int &a, int &b) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
    } else if (type == 5) { // BOTTOM
        a = n-1;
        b = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
    }
}

void rand_gen(int &a, int &b, int &c) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
        c = 3;
    } else if (type == 5) { // BOTTOM
        a = n-2;
        b = n-1;
        c = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
        do {
            c = rand() % n + 1;
        } while (c == a || c == b);
    }
}

std::string toString(std::chrono::steady_clock::duration tp)
{
    using namespace std;
    using namespace std::chrono;
    nanoseconds ns = duration_cast<nanoseconds>(tp);
    typedef duration<int, ratio<86400>> days;
    std::stringstream ss;
    char fill = ss.fill();
    ss.fill('0');
    auto d = duration_cast<days>(ns);
    ns -= d;
    auto h = duration_cast<hours>(ns);
    ns -= h;
    auto m = duration_cast<minutes>(ns);
    ns -= m;
    auto s = duration_cast<seconds>(ns);
    ns -= s;
    auto ms = duration_cast<milliseconds>(ns);
    // auto s = duration<float, std::ratio<1, 1>>(ns);
    if (d.count() > 0 || h.count() > 0)
        ss << "TOO_LONG & ";
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}

// std::string toString(int tp) // expect unit: ms
// {
//     using namespace std;
//     using namespace std::chrono;
//     milliseconds ns(tp);
//     typedef duration<int, ratio<86400>> days;
//     std::stringstream ss;
//     char fill = ss.fill();
//     ss.fill('0');
//     auto d = duration_cast<days>(ns);
//     ns -= d;
//     auto h = duration_cast<hours>(ns);
//     ns -= h;
//     auto m = duration_cast<minutes>(ns);
//     ns -= m;
//     auto s = duration_cast<seconds>(ns);
//     ns -= s;
//     auto ms = duration_cast<milliseconds>(ns);
//     // auto s = duration<float, std::ratio<1, 1>>(ns);
//     if (d.count() > 0 || h.count() > 0)
//         ss << "TOO_LONG & ";
//     else if (m.count() == 0 && s.count() < 10) {
//         ss << s.count() << '.' << ms.count() / 100 << "s";
//     } else {
//         if (m.count() > 0) ss << m.count() << 'm';
//         ss << s.count() << 's';// << " & ";
//     }
//     ss.fill(fill);
//     return ss.str();
// }

int main(int argc, char **argv) {
    type = atoi(argv[1]); // algorithm
    n = atoi(argv[2]); // the gate id / the number of qubits
    if (argc > 4) {
        VATA::Util::TreeAutomata::gateLog = true;
        VATA::Util::TreeAutomata::opLog = true;
    } else if (argc > 3) {
        if (strcmp(argv[3], "g") == 0)
            VATA::Util::TreeAutomata::gateLog = true;
        else if (strcmp(argv[3], "op") == 0)
            VATA::Util::TreeAutomata::opLog = true;
        else {
            cout << "Log not supported!" << endl;
            return 0;
        }
    }

    int stateBefore = 0, transitionBefore = 0;
    VATA::Util::TreeAutomata aut;
    VATA::Serialization::TimbukSerializer serializer;
    auto start = chrono::steady_clock::now();
    if (type == 0) {
        auto start = chrono::steady_clock::now();
        aut = VATA::Util::TreeAutomata::classical(10);
        n--;
        switch(n) {
            case 0: aut.X(1); break;
            case 1: aut.Y(1); break;
            case 2: aut.Z(1); break;
            case 3: aut.H(1); break;
            case 4: aut.S(1); break;
            case 5: aut.T(1); break;
            case 6: aut.Rx(1); break;
            case 7: aut.Ry(1); break;
            case 8: aut.CNOT(1, 2); break;
            case 9: aut.CZ(1, 2); break;
            case 10: aut.Toffoli(1, 2, 3); break;
            case 11: aut.Fredkin(1, 2, 3); break;
            default: break;
        }
        auto duration = chrono::steady_clock::now() - start;
        std::cout << toString(duration) << " & ";
        return 0;
    } else if (type == 1) { /* Algorithm 1 - Bernstein-Vazirani */
        aut = VATA::Util::TreeAutomata::zero(n+1);
        stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
        for (int i=1; i<=n+1; i++) aut.H(i);
        aut.Z(n+1);
        for (int i=1; i<=n; i++) {
            auto aut2 = aut;
            aut2.CNOT(i, n+1);
            aut = aut.Union(aut2);
        }
        for (int i=1; i<=n; i++) aut.H(i);
        std::ofstream fileLhs("/tmp/automata1.txt");
        aut.fraction_simplication();
        fileLhs << serializer.Serialize(aut);
        fileLhs.close();
        if (!VATA::Util::TreeAutomata::check_equal("/tmp/automata1.txt", "./reference_answers/Bernstein_Vazirani" + std::to_string(n) + ".txt")) {
            throw std::exception();
        }
    } else if (type == 7) { /* Algorithm 7 - randomly broken Bernstein-Vazirani */
        if (!(n >= 2)) throw std::out_of_range("");
        const int NUM_OF_LOOPS = 10;
        const int NUM_OF_PIPES = 10;
        int fd[2 * NUM_OF_PIPES];
        int total_stateBefore = 0;
        int total_stateNum = 0;
        int total_transitionBefore = 0;
        int total_transitionSize = 0;
        std::chrono::steady_clock::duration total_duration{};
        for (int z=0; z<NUM_OF_LOOPS; z++) {
            // Notice that we must put at least one rand() function in the parent process
            // to ensure the randomness among different iterations.
            int randGate = rand() % (2*n+2);
            for (int i=0; i<2*NUM_OF_PIPES; i+=2)
                pipe(fd+i); // create pipe descriptors
            if (fork() == 0) {
                auto start = chrono::steady_clock::now();
                aut = VATA::Util::TreeAutomata::zero(n+1);
                stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
                for (int i=1; i<=n+1; i++) {
                    if (randGate-- == 0) aut.randG(3, i);
                    else aut.H(i);
                }
                if (randGate-- == 0) aut.randG(2, n+1);
                else aut.Z(n+1);
                for (int i=1; i<=n; i++) {
                    auto aut2 = aut;
                    aut2.CNOT(i, n+1);
                    aut = aut.Union(aut2);
                }
                for (int i=1; i<=n; i++) {
                    if (randGate-- == 0) aut.randG(3, i);
                    else aut.H(i);
                }

                std::ofstream fileLhs("/tmp/automata1.txt");
                aut.fraction_simplication();
                fileLhs << serializer.Serialize(aut);
                fileLhs.close();
                if (VATA::Util::TreeAutomata::check_equal("/tmp/automata1.txt", "./reference_answers/Bernstein_Vazirani" + std::to_string(n) + ".txt")) {
                    std::cout << "An equivalent automaton appears!\n";
                }
                auto end = chrono::steady_clock::now();

                for (int i=0; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]); // child: writing only, so close read-descriptor.

                // send the value on the write-descriptor.
                write(fd[1], &aut.qubitNum, sizeof(aut.qubitNum));
                // printf("Child(%d) send value: %d\n", getpid(), aut.qubitNum);

                write(fd[3], &VATA::Util::TreeAutomata::gateCount, sizeof(VATA::Util::TreeAutomata::gateCount));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::gateCount);

                write(fd[5], &stateBefore, sizeof(stateBefore));
                // printf("Child(%d) send value: %d\n", getpid(), stateBefore);

                write(fd[7], &aut.stateNum, sizeof(aut.stateNum));
                // printf("Child(%d) send value: %d\n", getpid(), aut.stateNum);

                write(fd[9], &transitionBefore, sizeof(transitionBefore));
                // printf("Child(%d) send value: %d\n", getpid(), transitionBefore);

                int transition_size = aut.transition_size();
                write(fd[11], &transition_size, sizeof(transition_size));
                // printf("Child(%d) send value: %d\n", getpid(), transition_size);

                write(fd[13], &VATA::Util::TreeAutomata::binop_time, sizeof(VATA::Util::TreeAutomata::binop_time));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::binop_time);

                write(fd[15], &VATA::Util::TreeAutomata::branch_rest_time, sizeof(VATA::Util::TreeAutomata::branch_rest_time));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::branch_rest_time);

                write(fd[17], &VATA::Util::TreeAutomata::value_rest_time, sizeof(VATA::Util::TreeAutomata::value_rest_time));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::value_rest_time);

                std::chrono::steady_clock::duration duration = end - start;
                write(fd[19], &duration, sizeof(duration));
                // printf("Child(%d) send value: %d\n", getpid(), duration);

                // close the write descriptor
                for (int i=1; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]);
                exit(EXIT_SUCCESS);
            } else {
                // parent: reading only, so close the write-descriptor
                for (int i=1; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]);

                // now read the data (will block)
                read(fd[0], &aut.qubitNum, sizeof(aut.qubitNum));
                // printf("Parent(%d) received value: %d\n", getpid(), aut.qubitNum);
                
                read(fd[2], &VATA::Util::TreeAutomata::gateCount, sizeof(VATA::Util::TreeAutomata::gateCount));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::gateCount);

                read(fd[4], &stateBefore, sizeof(stateBefore));
                // printf("Parent(%d) received value: %d\n", getpid(), stateBefore);
                total_stateBefore += stateBefore;

                read(fd[6], &aut.stateNum, sizeof(aut.stateNum));
                // printf("Parent(%d) received value: %d\n", getpid(), aut.stateNum);
                total_stateNum += aut.stateNum;

                read(fd[8], &transitionBefore, sizeof(transitionBefore));
                // printf("Parent(%d) received value: %d\n", getpid(), transitionBefore);
                total_transitionBefore += transitionBefore;

                int transition_size;
                read(fd[10], &transition_size, sizeof(transition_size));
                // printf("Parent(%d) received value: %d\n", getpid(), transition_size);
                total_transitionSize += transition_size;

                read(fd[12], &VATA::Util::TreeAutomata::binop_time, sizeof(VATA::Util::TreeAutomata::binop_time));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::binop_time);

                read(fd[14], &VATA::Util::TreeAutomata::branch_rest_time, sizeof(VATA::Util::TreeAutomata::branch_rest_time));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::branch_rest_time);

                read(fd[16], &VATA::Util::TreeAutomata::value_rest_time, sizeof(VATA::Util::TreeAutomata::value_rest_time));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::value_rest_time);

                std::chrono::steady_clock::duration duration;
                read(fd[18], &duration, sizeof(duration));
                // printf("Parent(%d) received value: %d\n", getpid(), duration);
                total_duration += duration;

                // close the read-descriptor
                for (int i=0; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]);

                wait(nullptr);
            }
        }
        std::cout << n << " & " << VATA::Util::Convert::ToString(aut.qubitNum) << " & " << static_cast<float>(VATA::Util::TreeAutomata::gateCount) / NUM_OF_LOOPS << " & " << static_cast<float>(total_stateBefore) / NUM_OF_LOOPS << " & " << static_cast<float>(total_stateNum) / NUM_OF_LOOPS << " & " << static_cast<float>(total_transitionBefore) / NUM_OF_LOOPS << " & " << static_cast<float>(total_transitionSize) / NUM_OF_LOOPS
                    << " & " << VATA::Util::TreeAutomata::binop_time * 100 / total_duration
                    << "\\% & " << VATA::Util::TreeAutomata::branch_rest_time * 100 / total_duration
                    << "\\% & " << VATA::Util::TreeAutomata::value_rest_time * 100 / total_duration
                    << "\\% & " << toString(total_duration / NUM_OF_LOOPS) << "\\\\\\hline\n";
        return 0;
    } else if (type == 2) { /* Algorithm 2 - Grover's Search */
        if (!(n >= 2)) throw std::out_of_range("");
        aut = VATA::Util::TreeAutomata::classical_zero_one_zero(n);
        stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
        for (int i=1; i<=n; i++) aut.X(i);
        for (int i=n+1; i<=2*n+1; i++) aut.H(i);
        for (int iter=1; iter <= M_PI / (4 * asin(1 / pow(2, n/2.0))); iter++) {
            for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
            if (n >= 3) {
                aut.Toffoli(n+1, n+2, 2*n+2);
                for (int i=3; i<=n; i++)
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.CNOT(3*n, 2*n+1);
                for (int i=n; i>=3; i--)
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.Toffoli(n+1, n+2, 2*n+2);
            } else {
                if (!(n == 2)) throw std::out_of_range("");
                aut.Toffoli(3, 4, 5);
            }
            for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
            /****************************************/
            for (int i=n+1; i<=2*n; i++) aut.H(i);
            for (int i=n+1; i<=2*n; i++) aut.X(i);
            if (n >= 3) {
                aut.Toffoli(n+1, n+2, 2*n+2);
                for (int i=3; i<n; i++) // Note that < does not include n!
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.CZ(3*n-1, 2*n);
                for (int i=n-1; i>=3; i--)
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.Toffoli(n+1, n+2, 2*n+2);
            } else {
                if (!(n == 2)) throw std::out_of_range("");
                aut.CZ(3, 4);
            }
            for (int i=n+1; i<=2*n; i++) aut.X(i);
            for (int i=n+1; i<=2*n; i++) aut.H(i);
        }
        for (int i=1; i<=n; i++) aut.X(i);
        std::ofstream fileLhs("/tmp/automata1.txt");
        aut.fraction_simplication();
        fileLhs << serializer.Serialize(aut);
        fileLhs.close();
        if (!VATA::Util::TreeAutomata::check_equal("/tmp/automata1.txt", "./reference_answers/Grover" + std::to_string(n) + ".txt")) {
            throw std::exception();
        }
    } else if (type == 8) { /* Algorithm 8 - randomly broken Grover's Search */
        if (!(n >= 2)) throw std::out_of_range("");
        const int NUM_OF_LOOPS = 10;
        const int NUM_OF_PIPES = 10;
        int fd[2 * NUM_OF_PIPES];
        int total_stateBefore = 0;
        int total_stateNum = 0;
        int total_transitionBefore = 0;
        int total_transitionSize = 0;
        std::chrono::steady_clock::duration total_duration{};
        int ITER = M_PI / (4 * asin(1 / pow(2, n/2.0)));
        for (int z=0; z<NUM_OF_LOOPS; z++) {
            // Notice that we must put at least one rand() function in the parent process
            // to ensure the randomness among different iterations.
            int randGate = rand() % (n+1 + ITER*((n>=3) ? (6*n-3) : (4*n+1)));
            // n+1
            // ITER * (n + n +                                    + n + n)
            //                 if (n >= 3): 1 + n-3 + 1 + n-3 + 1
            //                        else: 1
            for (int i=0; i<2*NUM_OF_PIPES; i+=2)
                pipe(fd+i); // create pipe descriptors
            if (fork() == 0) {
                auto start = chrono::steady_clock::now();
                aut = VATA::Util::TreeAutomata::classical_zero_one_zero(n);
                stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
                for (int i=1; i<=n; i++) aut.X(i);
                for (int i=n+1; i<=2*n+1; i++) {
                    if (randGate-- == 0) aut.randG(3, i);
                    else aut.H(i);
                }
                for (int iter=1; iter<=ITER; iter++) {
                    for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
                    if (n >= 3) {
                        aut.Toffoli(n+1, n+2, 2*n+2);
                        for (int i=3; i<=n; i++)
                            aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                        aut.CNOT(3*n, 2*n+1);
                        for (int i=n; i>=3; i--)
                            aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                        aut.Toffoli(n+1, n+2, 2*n+2);
                    } else {
                        if (!(n == 2)) throw std::out_of_range("");
                        aut.Toffoli(3, 4, 5);
                    }
                    for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
                    /****************************************/
                    for (int i=n+1; i<=2*n; i++) {
                        if (randGate-- == 0) aut.randG(3, i);
                        else aut.H(i);
                    }
                    for (int i=n+1; i<=2*n; i++) {
                        if (randGate-- == 0) aut.randG(0, i);
                        else aut.X(i);
                    }
                    if (n >= 3) {
                        if (randGate-- == 0) aut.randG(10, n+1, n+2, 2*n+2);
                        else aut.Toffoli(n+1, n+2, 2*n+2);
                        for (int i=3; i<n; i++) { // Note that < does not include n!
                            if (randGate-- == 0) aut.randG(10, n+i, 2*n+i-1, 2*n+i);
                            else aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                        }
                        if (randGate-- == 0) aut.randG(9, 3*n-1, 2*n);
                        else aut.CZ(3*n-1, 2*n);
                        for (int i=n-1; i>=3; i--) {
                            if (randGate-- == 0) aut.randG(10, n+i, 2*n+i-1, 2*n+i);
                            else aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                        }
                        if (randGate-- == 0) aut.randG(10, n+1, n+2, 2*n+2);
                        else aut.Toffoli(n+1, n+2, 2*n+2);
                    } else {
                        if (!(n == 2)) throw std::out_of_range("");
                        if (randGate-- == 0) aut.randG(9, 3, 4);
                        else aut.CZ(3, 4);
                    }
                    for (int i=n+1; i<=2*n; i++) {
                        if (randGate-- == 0) aut.randG(0, i);
                        else aut.X(i);
                    }
                    for (int i=n+1; i<=2*n; i++) {
                        if (randGate-- == 0) aut.randG(3, i);
                        else aut.H(i);
                    }
                }
                for (int i=1; i<=n; i++) aut.X(i);
                std::ofstream fileLhs("/tmp/automata1.txt");
                aut.fraction_simplication();
                fileLhs << serializer.Serialize(aut);
                fileLhs.close();
                if (VATA::Util::TreeAutomata::check_equal("/tmp/automata1.txt", "./reference_answers/Grover" + std::to_string(n) + ".txt")) {
                    std::cout << "An equivalent automaton appears!\n";
                }
                auto end = chrono::steady_clock::now();

                for (int i=0; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]); // child: writing only, so close read-descriptor.

                // send the value on the write-descriptor.
                write(fd[1], &aut.qubitNum, sizeof(aut.qubitNum));
                // printf("Child(%d) send value: %d\n", getpid(), aut.qubitNum);

                write(fd[3], &VATA::Util::TreeAutomata::gateCount, sizeof(VATA::Util::TreeAutomata::gateCount));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::gateCount);

                write(fd[5], &stateBefore, sizeof(stateBefore));
                // printf("Child(%d) send value: %d\n", getpid(), stateBefore);

                write(fd[7], &aut.stateNum, sizeof(aut.stateNum));
                // printf("Child(%d) send value: %d\n", getpid(), aut.stateNum);

                write(fd[9], &transitionBefore, sizeof(transitionBefore));
                // printf("Child(%d) send value: %d\n", getpid(), transitionBefore);

                int transition_size = aut.transition_size();
                write(fd[11], &transition_size, sizeof(transition_size));
                // printf("Child(%d) send value: %d\n", getpid(), transition_size);

                write(fd[13], &VATA::Util::TreeAutomata::binop_time, sizeof(VATA::Util::TreeAutomata::binop_time));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::binop_time);

                write(fd[15], &VATA::Util::TreeAutomata::branch_rest_time, sizeof(VATA::Util::TreeAutomata::branch_rest_time));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::branch_rest_time);

                write(fd[17], &VATA::Util::TreeAutomata::value_rest_time, sizeof(VATA::Util::TreeAutomata::value_rest_time));
                // printf("Child(%d) send value: %d\n", getpid(), VATA::Util::TreeAutomata::value_rest_time);

                std::chrono::steady_clock::duration duration = end - start;
                write(fd[19], &duration, sizeof(duration));
                // printf("Child(%d) send value: %d\n", getpid(), duration);

                // close the write descriptor
                for (int i=1; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]);
                exit(EXIT_SUCCESS);
            } else {
                // parent: reading only, so close the write-descriptor
                for (int i=1; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]);

                // now read the data (will block)
                read(fd[0], &aut.qubitNum, sizeof(aut.qubitNum));
                // printf("Parent(%d) received value: %d\n", getpid(), aut.qubitNum);
                
                read(fd[2], &VATA::Util::TreeAutomata::gateCount, sizeof(VATA::Util::TreeAutomata::gateCount));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::gateCount);

                read(fd[4], &stateBefore, sizeof(stateBefore));
                // printf("Parent(%d) received value: %d\n", getpid(), stateBefore);
                total_stateBefore += stateBefore;

                read(fd[6], &aut.stateNum, sizeof(aut.stateNum));
                // printf("Parent(%d) received value: %d\n", getpid(), aut.stateNum);
                total_stateNum += aut.stateNum;

                read(fd[8], &transitionBefore, sizeof(transitionBefore));
                // printf("Parent(%d) received value: %d\n", getpid(), transitionBefore);
                total_transitionBefore += transitionBefore;

                int transition_size;
                read(fd[10], &transition_size, sizeof(transition_size));
                // printf("Parent(%d) received value: %d\n", getpid(), transition_size);
                total_transitionSize += transition_size;

                read(fd[12], &VATA::Util::TreeAutomata::binop_time, sizeof(VATA::Util::TreeAutomata::binop_time));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::binop_time);

                read(fd[14], &VATA::Util::TreeAutomata::branch_rest_time, sizeof(VATA::Util::TreeAutomata::branch_rest_time));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::branch_rest_time);

                read(fd[16], &VATA::Util::TreeAutomata::value_rest_time, sizeof(VATA::Util::TreeAutomata::value_rest_time));
                // printf("Parent(%d) received value: %d\n", getpid(), VATA::Util::TreeAutomata::value_rest_time);

                std::chrono::steady_clock::duration duration;
                read(fd[18], &duration, sizeof(duration));
                // printf("Parent(%d) received value: %d\n", getpid(), duration);
                total_duration += duration;

                // close the read-descriptor
                for (int i=0; i<2*NUM_OF_PIPES; i+=2)
                    close(fd[i]);

                wait(nullptr);
            }
        }
        std::cout << n << " & " << VATA::Util::Convert::ToString(aut.qubitNum) << " & " << static_cast<float>(VATA::Util::TreeAutomata::gateCount) / NUM_OF_LOOPS << " & " << static_cast<float>(total_stateBefore) / NUM_OF_LOOPS << " & " << static_cast<float>(total_stateNum) / NUM_OF_LOOPS << " & " << static_cast<float>(total_transitionBefore) / NUM_OF_LOOPS << " & " << static_cast<float>(total_transitionSize) / NUM_OF_LOOPS
                    << " & " << VATA::Util::TreeAutomata::binop_time * 100 / total_duration
                    << "\\% & " << VATA::Util::TreeAutomata::branch_rest_time * 100 / total_duration
                    << "\\% & " << VATA::Util::TreeAutomata::value_rest_time * 100 / total_duration
                    << "\\% & " << toString(total_duration / NUM_OF_LOOPS) << "\\\\\\hline\n";
        return 0;
    } else if (type >= 3) { /* Algorithm 3 - Random Circuit */
        if (!(n >= 3)) throw std::out_of_range("");
        auto start = chrono::steady_clock::now();
        aut = VATA::Util::TreeAutomata::classical(n);
        for (int i=0; i<3*n; i++) {
            int a, b, c;
            switch(rand() % 12) {
                case 0: aut.X(rand_gen()); break;
                case 1: aut.Y(rand_gen()); break;
                case 2: aut.Z(rand_gen()); break;
                case 3: aut.H(rand_gen()); break;
                case 4: aut.S(rand_gen()); break;
                case 5: aut.T(rand_gen()); break;
                case 6: aut.Rx(rand_gen()); break;
                case 7: aut.Ry(rand_gen()); break;
                case 8: rand_gen(a, b); aut.CNOT(a, b); break;
                case 9: rand_gen(a, b); aut.CZ(a, b); break;
                case 10: rand_gen(a, b, c); aut.Toffoli(a, b, c); break;
                case 11: rand_gen(a, b, c); aut.Fredkin(a, b, c); break;
                default: break;
            }
        }
        auto duration = chrono::steady_clock::now() - start;
        std::cout << " & " << toString(duration);
        return 0;
    }
    auto end = chrono::steady_clock::now();
    auto duration = end - start;
    std::cout << n << " & " << VATA::Util::Convert::ToString(aut.qubitNum) << " & " << VATA::Util::TreeAutomata::gateCount << " & " << stateBefore << " & " << aut.stateNum << " & " << transitionBefore << " & " << aut.transition_size()
                    << " & " << VATA::Util::TreeAutomata::binop_time * 100 / duration
                    << "\\% & " << VATA::Util::TreeAutomata::branch_rest_time * 100 / duration
                    << "\\% & " << VATA::Util::TreeAutomata::value_rest_time * 100 / duration
                    << "\\% & " << toString(duration) << "\\\\\\hline\n";
    // std::cout << /*n << ": " <<*/ chrono::duration_cast<chrono::milliseconds>(end - start).count() << " & ";
    return 0;
}
