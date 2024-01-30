#include <autoq/aut_description.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/util/util.hh>
#include <autoq/inclusion.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <fstream>
#include <filesystem>

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::execute(const std::string& filename) {
    bool verify = true;
    bool inGateDef = false;
    bool inWhileLoop = false;
    bool inIfBlock = false;
    bool inElseBlock = false;
    std::map<std::string, int> var_is_measure_what_qubit;
    std::string while_measurement_guard;
    AUTOQ::Automata<Symbol> I, measure_to_continue, measure_to_break, measure_to_else, result_after_if;
    std::ifstream qasm(filename);
    const std::regex digit("\\d+");
    const std::regex_iterator<std::string::iterator> END;
    if (!qasm.is_open()) throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] Failed to open file " + std::string(filename) + ".");
    std::string line, previous_line;
    while (getline(qasm, line)) {
        line = AUTOQ::Util::trim(line);
        if (inGateDef) {
            if (line.find("}") != std::string::npos) {
                inGateDef = false;
            }
            continue; // simply ignore gate definitions
        }
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0 || line.find("//") == 0 || line.find("/*") == 0 || line.find("bit") == 0) continue;
        if (line.find("qreg ") == 0 || line.find("qubit") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            while (it != END) {
                if (atoi(it->str().c_str()) != static_cast<int>(qubitNum))
                    throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The number of qubits in the automaton does not match the number of qubits in the circuit.");
                ++it;
            }
        } else if (line.find("x ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                X(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("y ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Y(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("z ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Z(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("h ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                H(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("s ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                S(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("sdg ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Sdg(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("t ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                T(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("tdg ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Tdg(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("rx(pi/2) ") == 0 || line.find("rx(pi / 2)") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Rx(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Ry(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("cx ") == 0 || line.find("CX ") == 0 ) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CNOT(pos[0], pos[1]);
        } else if (line.find("cz ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CZ(pos[0], pos[1]);
        } else if (line.find("ck ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CK(pos[0], pos[1]);
        } else if (line.find("ccx ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            Toffoli(pos[0], pos[1], pos[2]);
        } else if (line.find("swap ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            swap(pos[0], pos[1]);
        } else if (line.find("while") == 0) { // while (!result) { // loop-invariant.{spec|hsl}
            if (previous_line.find("measure") == std::string::npos)
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The while loop guard must be a measurement operator.");
            while_measurement_guard = previous_line;
            std::erase(while_measurement_guard, ' ');
            inWhileLoop = true;
            const std::regex varR("\\((.*)\\)");
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), varR);
            assert(it != END);
            std::string var = AUTOQ::Util::trim(it->str(1));
            bool negate = (var.at(0) == '!'); // whether the variable is negated
            if (negate)
                var = var.substr(1);
            int pos = var_is_measure_what_qubit[var];
            /********************************/
            const std::regex spec("// *(.*)");
            std::regex_iterator<std::string::iterator> it2(line.begin(), line.end(), spec);
            std::string dir = (std::filesystem::current_path() / filename).parent_path().string();
            I = AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomaton(dir + std::string("/") + it2->str(1));
            /**************************************************************************************************************/
            // std::cout << "We first verify \"P ⊆ I\" here." << std::endl;
            // this->print_language("P:\n");
            // I.print_language("I:\n");
            this->remove_useless(); this->reduce(); I.remove_useless(); I.reduce();
            bool t = is_scaled_spec_satisfied(*this, I);
            verify &= t;
            if (!t) {
                AUTOQ_ERROR("[ERROR] P ⊈ I.");
                fraction_simplification();
                print_language("P:\n");
                I.fraction_simplification();
                I.print_language("I:\n");
            }
            if (negate) {
                measure_to_continue = I.measure(pos, false);
                measure_to_break = I.measure(pos, true);
            } else { // while (measure ...
                measure_to_continue = I.measure(pos, true);
                measure_to_break = I.measure(pos, false);
            }
            *this = measure_to_continue;
        } else if (line.find("}") == 0) {
            if (inWhileLoop) {
                inWhileLoop = false;
                std::erase(previous_line, ' ');
                if (while_measurement_guard != previous_line)
                    throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The while loop guard must be repeated at the end of the loop!");
                // const std::regex spec("// *(.*)");
                // std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), spec);
                // std::string dir = (std::filesystem::current_path() / filename).parent_path().string();
                // auto Q = AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomaton(dir + std::string("/") + it->str(1));
                /**************************************************************************************************************/
                // measure_to_continue = *this; // is C(measure_to_continue)
                // std::cout << "Then we verify \"C(measure_to_continue) ⊆ I\" here." << std::endl;
                // measure_to_continue.print_language("C(measure_to_continue):\n");
                // I.print_language("I:\n");
                // measure_to_continue.remove_useless(); measure_to_continue.reduce(); // I.remove_useless(); I.reduce();
                bool t = is_scaled_spec_satisfied(*this, I);
                verify &= t;
                if (!t) {
                    AUTOQ_ERROR("[ERROR] C(measure_to_continue) ⊈ I.");
                    fraction_simplification();
                    print_language("C(measure_to_continue):\n");
                    I.fraction_simplification();
                    I.print_language("I:\n");
                }
                // std::cout << "Then we verify \"measure_to_break ⊆ Q\" here." << std::endl;
                // measure_to_break.print_language("measure_to_break:\n");
                // Q.print_language("Q:\n");
                // measure_to_break.remove_useless(); measure_to_break.reduce(); Q.remove_useless(); Q.reduce();
                // t = is_scaled_spec_satisfied(measure_to_break, constraintI, Q, constraintQ);
                // verify &= t;
                // if (!t) AUTOQ_ERROR("[ERROR] measure_to_break ⊈ Q.");
                *this = measure_to_break; // Use this postcondition to execute the remaining circuit!
                gateCount--; // retract the excess counting of the measurement operator in the while loop guard
            } else if (inIfBlock) {
                inIfBlock = false;
                result_after_if = *this; // this automaton is used to be merged with the result automaton after the "else" block if the "else" block is present.
                *this = this->Union(measure_to_else); // if the "else" block is absent, then that branch is simply the other measurement outcome.
            } else if (inElseBlock) {
                inElseBlock = false;
                *this = this->Union(result_after_if); // merge the else-branch result with the if-branch result
            }
        } else if (line.find("if") == 0) { // if (!result) {
            if (previous_line.find("measure") == std::string::npos)
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The if guard must be a measurement operator.");
            inIfBlock = true;
            const std::regex varR("\\((.*)\\)");
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), varR);
            assert(it != END);
            std::string var = AUTOQ::Util::trim(it->str(1));
            bool negate = (var.at(0) == '!'); // whether the variable is negated
            if (negate)
                var = var.substr(1);
            int pos = var_is_measure_what_qubit[var];
            if (negate) {
                measure_to_else = this->measure(pos, true);
                *this = this->measure(pos, false);
            } else { // if (measure ...
                measure_to_else = this->measure(pos, false);
                *this = this->measure(pos, true);
            }
        } else if (line.find("else") == 0) { // else {
            inElseBlock = true;
            *this = measure_to_else;
        } else if (line.find("gate ") == 0) {
            if (line.find("}") == std::string::npos) {
                inGateDef = true; // TODO: unsure if this is necessary
            }
        } else if (line.find("=") != std::string::npos && line.find("measure") != std::string::npos) {
            const std::regex m("([^ ]+) *= *measure.*\\[(\\d+)\\]"); // result = measure problem[4];
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), m);
            assert(it != END);
            std::string result = it->str(1);
            int pos = 1 + atoi(it->str(2).c_str());
            var_is_measure_what_qubit[result] = pos;
            // TODO: Actually, we should split the automaton here into two separate copies which
            // are produced from the measurement outcome of 0 and 1, respectively. However, we do
            // not do this for simplicity temporarily.
        } else if (line.length() > 0)
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] unsupported gate: " + line + ".");
        // fraction_simplification();
        // print("\n" + line + "\n");
        // print_language(("\n" + line + "\n").c_str());
        if (line.length() > 0)
            previous_line = line;
    }
    qasm.close();
    return verify;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;