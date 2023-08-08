#ifndef _AUTOQ_COMPLEX_PARSER_HH_
#define _AUTOQ_COMPLEX_PARSER_HH_

#include <iostream>
#include <string>
#include <cctype>
#include <cmath>
#include <boost/rational.hpp>
#include "autoq/complex/complex.hh"

using AUTOQ::Complex::Complex;

class StringParser {
public:
    StringParser(const std::string& input) : input_(input), index_(0) {}

    Complex parse() {
        skipWhitespace();
        Complex result = parseExpression();
        return result;
    }

private:
    const std::string& input_;
    size_t index_;

    void skipWhitespace() {
        while (index_ < input_.length() && std::isspace(input_[index_])) {
            index_++;
        }
    }

    Complex parseExpression() {
        Complex left = parseTerm();
        while (index_ < input_.length()) {
            skipWhitespace();
            char op = input_[index_];
            if (op == '+' || op == '-') {
                index_++;
                Complex right = parseTerm();
                if (op == '+') {
                    left = left + right;
                } else {
                    left = left - right;
                }
            } else {
                break;
            }
        }
        return left;
    }

    Complex parseTerm() {
        Complex left = parseFactor();
        while (index_ < input_.length()) {
            skipWhitespace();
            char op = input_[index_];
            if (op == '*' || op == '/') {
                index_++;
                Complex right = parseFactor();
                if (op == '*') {
                    left = left * right;
                } else {
                    if (right != Complex(0)) {
                        // assert(right.imag() == 0);
                        assert(right.real().denominator() == 1);
                        auto n = right.real().numerator();
                        while (n > 0) {
                            assert(n % 2 == 0); // Assume the denominator is a power of two.
                            left.divide_by_the_square_root_of_two(2);
                            n /= 2;
                        }
                    } else {
                        throw std::runtime_error("Division by zero");
                    }
                }
            } else {
                break;
            }
        }
        return left;
    }

    Complex fastPower(Complex base, int exponent) {
        assert(exponent >= 0);
        if (exponent == 0) return 1;
        if (exponent % 2 == 0) {
            Complex temp = fastPower(base, exponent / 2);
            return temp * temp;
        } else {
            Complex temp = fastPower(base, (exponent - 1) / 2);
            return base * temp * temp;
        }
    }
    Complex parseFactor() {
        Complex base = parsePrimary();
        if (index_ < input_.length() && input_[index_] == '^') {
            index_++;
            Complex exponent = parseFactor();
            // assert(exponent.imag() == 0); // Assume the exponent must be an integer.
            assert(exponent.real().denominator() == 1);
            return fastPower(base, static_cast<int>(exponent.real().numerator()));
        }
        return base;
    }

    Complex parsePrimary() {
        skipWhitespace();
        if (index_ >= input_.length()) {
            throw std::runtime_error("Unexpected end of input");
        }
        if (input_[index_] == '(') {
            index_++;
            Complex result = parseExpression();
            if (index_ >= input_.length() || input_[index_] != ')') {
                throw std::runtime_error("Missing closing parenthesis");
            }
            index_++;
            return result;
        } else if (std::isalpha(input_[index_])) {
            size_t start = index_;
            while (index_ < input_.length() && (std::isalpha(input_[index_]) || std::isdigit(input_[index_]) || input_[index_] == '.')) {
                index_++;
            }
            std::string function = input_.substr(start, index_ - start);
            if (function == "A") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    skipWhitespace();
                    if (index_ >= input_.length() || !std::isdigit(input_[index_]) && input_[index_] != '-') {
                        throw std::runtime_error("Invalid argument for A function");
                    }
                    auto x = parseNumber();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        throw std::runtime_error("Missing closing parenthesis for A function");
                    }
                    index_++;
                    return Complex::Angle(x);
                } else {
                    throw std::runtime_error("Invalid syntax for A function");
                }
            } else if (function == "V2") {
                return Complex::sqrt2();
            } else {
                throw std::runtime_error("Unknown function: " + function);
            }
        } else if (std::isdigit(input_[index_]) || input_[index_] == '-') {
            return Complex(parseNumber());
        } else {
            throw std::runtime_error("Unexpected character: " + std::string(1, input_[index_]));
        }
    }

    boost::rational<boost::multiprecision::cpp_int> parseNumber() {
        size_t start = index_;
        while (index_ < input_.length() && (std::isdigit(input_[index_]) || input_[index_] == '.' || input_[index_] == '-')) {
            index_++;
        }
        std::string numStr = input_.substr(start, index_ - start);
        int d = 0;
        for (int i=numStr.length()-1; i>=0; i--) {
            if (numStr.at(i) == '.') {
                d = numStr.length()-1 - i;
                numStr.erase(i, 1);
                break; // assume only one decimal point
            }
        }
        return boost::rational<boost::multiprecision::cpp_int>(boost::multiprecision::cpp_int(numStr), boost::multiprecision::pow(boost::multiprecision::cpp_int(10), d));
    }
};

int main() {
    std::string expression("3 + 2 * (A(0.5) * 4 + V2^6) + 7/2");
    std::cout << "Enter an arithmetic expression: ";
    // std::getline(std::cin, expression);

    StringParser parser(expression);
    try {
        Complex result = parser.parse();
        std::cout << "Result: " << result << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
    }

    return 0;
}

#endif