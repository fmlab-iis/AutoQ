#ifndef _AUTOQ_COMPLEX_PARSER_HH_
#define _AUTOQ_COMPLEX_PARSER_HH_

#include <iostream>
#include <string>
#include <cctype>
#include <cmath>
#include <boost/rational.hpp>
#include "autoq/complex/complex.hh"

using AUTOQ::Complex::Complex;

typedef boost::rational<boost::multiprecision::cpp_int> rational;

class ComplexParser {
public:
    ComplexParser(const std::string &input) : input_(input), index_(0), resultC(), resultV(), constMap_(constMap2), unknownVariableErrorOccurred(false) {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    ComplexParser(const std::string &input, const std::map<std::string, Complex> &constMap) : input_(input), index_(0), resultC(), resultV(), constMap_(constMap), unknownVariableErrorOccurred(false) {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    Complex getComplex() const {
        return resultC;
    }
    std::string getConstName() const {
        return resultV;
    }

private:
    std::string input_;
    size_t index_;
    Complex resultC; // complex
    std::string resultV; // variable
    const std::map<std::string, Complex> &constMap_;
    const std::map<std::string, Complex> constMap2{}; // empty only for initialization
    bool unknownVariableErrorOccurred;

    void parse() {
        try {
            resultC = parseExpression();
        } catch (std::exception& e) {
            if (!unknownVariableErrorOccurred) {
            // for (char c : input_) {
            //     if (!std::isalnum(c)) {
                    std::cerr << e.what() << std::endl;
                    throw e;
            //     }
            // }
            }
            resultV = input_;
        }
    }

    Complex parseExpression() {
        Complex left = parseTerm();
        while (index_ < input_.length()) {
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
            char op = input_[index_];
            if (op == '*' || op == '/') {
                index_++;
                Complex right = parseFactor();
                if (op == '*') {
                    left = left * right;
                } else {
                    if (!right.isZero()) {
                        left = left / right;
                    } else {
                        THROW_AUTOQ_ERROR("Division by zero");
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
        char nextChar = input_[index_];

        // Handle unary minus
        if (nextChar == '-')
            index_++;

        Complex left = parsePrimary();
        while (index_ < input_.length()) {
            char op = input_[index_];
            if (op == '^') {
                index_++;
                Complex right = parsePrimary();
                if (nextChar == '-')
                    return fastPower(left, static_cast<int>(right.toInt())) * -1;
                else
                    return fastPower(left, static_cast<int>(right.toInt()));
            } else {
                break;
            }
        }
        if (nextChar == '-')
            return left * -1;
        else
            return left;
    }

    // template <typename T>
    // rational others_to_rational(const T &in) {
    //     if constexpr(std::is_convertible_v<T, rational>)
    //         return rational(in);
    //     else // temporary conversion for double, may need additional enhancements
    //         return rational(static_cast<boost::multiprecision::cpp_int>(in * 1000000), 1000000);
    // }
    Complex parsePrimary() {
        if (index_ >= input_.length()) {
            THROW_AUTOQ_ERROR("Unexpected end of input");
        }
        if (input_[index_] == '(') {
            index_++;
            Complex result = parseExpression();
            if (index_ >= input_.length() || input_[index_] != ')') {
                THROW_AUTOQ_ERROR("Missing closing parenthesis");
            }
            index_++;
            return result;
        } else if (std::isalpha(input_[index_])) {
            size_t start = index_;
            while (index_ < input_.length() && (std::isalpha(input_[index_]) || std::isdigit(input_[index_]) || input_[index_] == '.')) {
                index_++;
            }
            std::string function = input_.substr(start, index_ - start);
            if (function == "ei2pi") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length() || (!std::isdigit(input_[index_]) && input_[index_] != '-')) {
                        THROW_AUTOQ_ERROR("Invalid argument for ei2pi function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for ei2pi function");
                    }
                    index_++;
                    // assert(x.imag() == 0);
                    return Complex::Angle(x.to_rational());
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for ei2pi function");
                }
            } else if (function == "eipi") {
                if (index_ < input_.length() && input_[index_] == '(') {
                    index_++;
                    if (index_ >= input_.length() || (!std::isdigit(input_[index_]) && input_[index_] != '-')) {
                        THROW_AUTOQ_ERROR("Invalid argument for eipi function");
                    }
                    auto x = parseExpression();
                    if (index_ >= input_.length() || input_[index_] != ')') {
                        THROW_AUTOQ_ERROR("Missing closing parenthesis for eipi function");
                    }
                    index_++;
                    // assert(x.imag() == 0);
                    return Complex::Angle(x.to_rational() / 2);
                } else {
                    THROW_AUTOQ_ERROR("Invalid syntax for eipi function");
                }
            } else if (function == "sqrt2") {
                return Complex::sqrt2();
            } else if (constMap_.count(function) > 0) { // may contain i
                return constMap_.at(function);
            } else if (function == "i") {
                return Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(1, 4));
            } else {
                unknownVariableErrorOccurred = true;
                THROW_AUTOQ_ERROR("Unknown variable: " + function);
            }
        } else if (std::isdigit(input_[index_]) || input_[index_] == '-') {
            return Complex(parseNumber());
        } else {
            THROW_AUTOQ_ERROR("Unexpected character: " + std::string(1, input_[index_]));
        }
    }

    rational parseNumber() {
        size_t start = index_;
        if (index_ < input_.length() && input_[index_] == '-')
            index_++;
        while (index_ < input_.length() && (std::isdigit(input_[index_]) || input_[index_] == '.')) {
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
        if (numStr.at(0) == '-') {
            while (numStr.at(1) == '0' && numStr.length() >= 3)
                numStr.erase(1, 1);
        } else {
            while (numStr.at(0) == '0' && numStr.length() >= 2)
                numStr.erase(0, 1);
        }
        return rational(boost::multiprecision::cpp_int(numStr), boost::multiprecision::pow(boost::multiprecision::cpp_int(10), d));
    }
};

#endif