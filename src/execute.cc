#include <autoq/util/string.hh>
#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/parsing/timbuk_parser.hh"
#include "autoq/parsing/complex_parser.hh"
#include <regex>
#include <fstream>
#include <filesystem>

template <typename Symbol>
void AUTOQ::Automata<Symbol>::execute(const std::string& filename, ParameterMap &params) {
    execute(filename.c_str(), params);
}
template <typename Symbol>
void AUTOQ::Automata<Symbol>::execute(const char *filename, ParameterMap &params) {
    initialize_stats();

    std::ifstream qasm(filename);
    const std::regex digit("\\d+");
    const std::regex rx(R"(rx\((.+)\).+\[(\d+)\];)");
    const std::regex rz(R"(rz\((.+)\).+\[(\d+)\];)");
    const std::regex_iterator<std::string::iterator> END;
    if (!qasm.is_open()) THROW_AUTOQ_ERROR("Failed to open file " + std::string(filename) + ".");
    std::string line, previous_line;
    // int lineno = 1;
    while (getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        // AUTOQ_DEBUG("[" << (lineno++) << "]: " << line);
        std::smatch match_rx; std::regex_search(line, match_rx, rx);
        std::smatch match_rz; std::regex_search(line, match_rz, rz);
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0|| line.find("//") == 0) continue;
        if (line.find("qreg ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            while (it != END) {
                if (atoi(it->str().c_str()) != static_cast<int>(qubitNum))
                    THROW_AUTOQ_ERROR("The number of qubits in the automaton does not match the number of qubits in the circuit.");
                ++it;
            }
        } else if (line.find("x ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            X(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("y ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            Y(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("z ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            Z(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("h ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            H(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("s ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            S(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("sdg ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            Sdg(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("t ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            T(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("tdg ") == 0) {
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, digit);
            Tdg(1 + atoi(match_pieces[0].str().c_str()));
        } else if (match_rx.size() == 3) {
            std::string angle = match_rx[1];
            size_t pos = angle.find("pi");
            if (pos != std::string::npos) {
                angle.replace(pos, 2, "(1/2)");
            } else if (angle != "0") {
                THROW_AUTOQ_ERROR("The angle in rx gate is not a multiple of pi!");
            }
            std::string qubit = match_rx[2];
            // AUTOQ_DEBUG("rx(" << angle << ") @ " << qubit);
            Rx(ComplexParser(angle).getComplex().to_rational(), 1 + atoi(qubit.c_str()));
        } else if (match_rz.size() == 3) {
            std::string angle = match_rz[1];
            size_t pos = angle.find("pi");
            if (pos != std::string::npos) {
                angle.replace(pos, 2, "(1/2)");
            } else if (angle != "0") {
                THROW_AUTOQ_ERROR("The angle in rz gate is not a multiple of pi!");
            }
            std::string qubit = match_rz[2];
            // AUTOQ_DEBUG("rz(" << angle << ") @ " << qubit);
            Rz(ComplexParser(angle).getComplex().to_rational(), 1 + atoi(qubit.c_str()));
        } else if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            // AUTOQ_DEBUG("ry(pi/2) @ " << pos[1]);
            Ry(pos[1]);
        } else if (line.find("cx ") == 0 || line.find("CX ") == 0 ) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CX(pos[0], pos[1]);
        } else if (line.find("cz ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CZ(pos[0], pos[1]);
        } else if (line.find("ccx ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CCX(pos[0], pos[1], pos[2]);
        } else if (line.find("swap ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            Swap(pos[0], pos[1]);
        } else if (line.find("PRINT_STATS") == 0) {
            print_stats(previous_line, true);
        } else if (line.find("PRINT_AUT") == 0) {
            print_aut();
        } else if (line.find("STOP") == 0) {
            break;
        } else if (line.length() > 0)
            THROW_AUTOQ_ERROR("unsupported gate: " + line + ".");
        previous_line = line;
        // print_stats(previous_line, true);
        stop_execute = std::chrono::steady_clock::now();
    }
    qasm.close();
}

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::reverse_execute(const char *filename) {
//     // initialize_stats();

//     std::ifstream qasm(filename);
//     const std::regex digit("\\d+");
//     const std::regex_iterator<std::string::iterator> END;
//     if (!qasm.is_open()) THROW_AUTOQ_ERROR("Failed to open file " + std::string(filename) + ".");
//     std::string line, previous_line;
//     std::vector<std::string> lines;
//     while (getline(qasm, line)) {
//         lines.push_back(line);
//     } // use the reverse iterator to read the file in reverse order
//     for (auto rit = lines.rbegin(); rit != lines.rend(); ++rit) {
//         line = *rit;
//         if (line.find("OPENQASM") == 0 || line.find("include ") == 0|| line.find("//") == 0) continue;
//         if (line.find("qreg ") == 0) {
//             continue;
//             // std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
//             // while (it != END) {
//             //     if (atoi(it->str().c_str()) != static_cast<int>(qubitNum))
//             //         THROW_AUTOQ_ERROR("The number of qubits in the automaton does not match the number of qubits in the circuit.");
//             //     ++it;
//             // }
//         } else if (line.find("x ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 X(1 + atoi(match_pieces[0].str().c_str())); // X = X^-1
//         } else if (line.find("y ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 Ydg(1 + atoi(match_pieces[0].str().c_str())); // Y = Y^-1
//         } else if (line.find("z ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 Z(1 + atoi(match_pieces[0].str().c_str())); // Z = Z^-1
//         } else if (line.find("h ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 H(1 + atoi(match_pieces[0].str().c_str())); // H = H^-1
//         } else if (line.find("s ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 Sdg(1 + atoi(match_pieces[0].str().c_str())); // Sdg = S^-1
//         } else if (line.find("sdg ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 S(1 + atoi(match_pieces[0].str().c_str())); // S = Sdg^-1
//         } else if (line.find("t ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 Tdg(1 + atoi(match_pieces[0].str().c_str())); // Tdg = T^-1
//         } else if (line.find("tdg ") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 T(1 + atoi(match_pieces[0].str().c_str())); // T = Tdg^-1
//         } else if (line.find("rx(pi/2) ") == 0 || line.find("rx(pi / 2)") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 Rx(1 + atoi(match_pieces[0].str().c_str()));
//         } else if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
//             std::smatch match_pieces;
//             std::regex_search(line, match_pieces, digit);
//                 Ry(1 + atoi(match_pieces[0].str().c_str()));
//         } else if (line.find("cx ") == 0 || line.find("CX ") == 0 ) {
//             std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
//             std::vector<int> pos;
//             while (it != END) {
//                 pos.push_back(1 + atoi(it->str().c_str()));
//                 ++it;
//             }
//             CX(pos[0], pos[1]); // CX = CX^-1
//         } else if (line.find("cz ") == 0) {
//             std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
//             std::vector<int> pos;
//             while (it != END) {
//                 pos.push_back(1 + atoi(it->str().c_str()));
//                 ++it;
//             }
//             CZ(pos[0], pos[1]); // CZ = CZ^-1
//         } else if (line.find("ccx ") == 0) {
//             std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
//             std::vector<int> pos;
//             while (it != END) {
//                 pos.push_back(1 + atoi(it->str().c_str()));
//                 ++it;
//             }
//             CCX(pos[0], pos[1], pos[2]); // CCX = CCX^-1
//         } else if (line.find("swap ") == 0) {
//             std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
//             std::vector<int> pos;
//             while (it != END) {
//                 pos.push_back(1 + atoi(it->str().c_str()));
//                 ++it;
//             }
//             Swap(pos[0], pos[1]); // SWAP = SWAP^-1
//         } else if (line.find("PRINT_STATS") == 0) {
//             print_stats(previous_line, true);
//         } else if (line.find("PRINT_AUT") == 0) {
//             print_aut();
//         } else if (line.find("STOP") == 0) {
//             break;
//         } else if (line.length() > 0)
//             THROW_AUTOQ_ERROR("unsupported gate: " + line + ".");
//         previous_line = line;
//         stop_execute = std::chrono::steady_clock::now();
//     }
//     qasm.close();
// }

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;