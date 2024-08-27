#ifndef _AUTOQ_ERROR_HH_
#define _AUTOQ_ERROR_HH_

#include "autoq/autoq.hh"
#include <stdexcept>

// Define your custom exception class that extends std::runtime_error
struct AutoQError : public std::runtime_error {
    // Constructor that passes the error message to std::runtime_error
    explicit AutoQError(const std::string &message)
        : std::runtime_error(message) {}
};

#define THROW_AUTOQ_ERROR(message) throw AutoQError("[ERROR] " + AUTOQ_LOG_PREFIX + message)

#endif