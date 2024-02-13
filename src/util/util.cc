/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Implementation of miscellaneous utility gadgets.
 *
 *****************************************************************************/

// AUTOQ headers
#include "autoq/autoq.hh"
#include "autoq/util/util.hh"

// Standard library headers
#include <regex>
#include <fstream>
#include <sys/types.h>
#include <sys/wait.h>

/**
 * @brief  Trim whitespaces from a string (both left and right)
 */
std::string AUTOQ::Util::trim(const std::string& str)
{
	std::string result = str;

	// trim from start
	result.erase(result.begin(), std::find_if(result.begin(), result.end(),
		[](int ch) {return !std::isspace(ch);}));

	// trim from end
	result.erase(std::find_if(result.rbegin(), result.rend(),
		[](int ch) {return !std::isspace(ch);}).base(), result.end());

	return result;
}

std::string AUTOQ::Util::ReadFile(const std::string& fileName)
{
	std::ifstream t(fileName);
	if (!t)
	{	// in case the file could not be open
		throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] Failed to open file " + fileName + ".");
	}

	std::string str;

	t.seekg(0, std::ios::end);
	str.reserve(t.tellg());
	t.seekg(0, std::ios::beg);

	str.assign((std::istreambuf_iterator<char>(t)),
		std::istreambuf_iterator<char>());

	return str;
}

// const int MAX_ARG_STRLEN = 131070; // in fact is 131072 on the Internet
std::string AUTOQ::Util::ShellCmd(const std::string &cmd) {
    // int length = cmd.length();
    // if (length > MAX_ARG_STRLEN) {
    //     std::vector<std::string> args;
    //     for (int i=0; i<length; i+=MAX_ARG_STRLEN) {
    //         args.push_back(cmd.substr(i, MAX_ARG_STRLEN));
    //     }
    //     return AUTOQ::Util::ShellCmd(args);
    // }

    char buffer[512];
    std::string result = "";

    // Open pipe to file
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        std::cout << cmd << std::endl;
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "popen() failed!");
    }

    // read till end of process:
    while (!feof(pipe)) {
        // use buffer to read and add to result
        if (fgets(buffer, sizeof(buffer), pipe) != NULL)
            result += buffer;
    }

    pclose(pipe);
    return result;
}
std::string AUTOQ::Util::ShellCmd(const std::vector<std::string> &cmd) {
    int pipefd[2];
    std::string result = "";

    if (pipe(pipefd) == -1) {
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "popen() failed!");
    }

    pid_t pid = fork();
    if (pid == -1) {
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "fork() failed!");
    } else if (pid == 0) { // Child process
        close(pipefd[0]); // Close unused read end
        // Redirect standard output to the write end of the pipe
        dup2(pipefd[1], STDOUT_FILENO);

        // Execute the command with the provided arguments
        // const char* args[] = {"ls", "-l", nullptr};  // Replace with your desired arguments
        // Create an array of const char* to hold the converted arguments
        const char** args = new const char*[cmd.size() + 1]; // +1 for the terminating nullptr
        for (size_t i = 0; i < cmd.size(); ++i)
            args[i] = cmd[i].c_str();
        args[cmd.size()] = nullptr; // Terminating nullptr
        // for (size_t i = 0; i < cmd.size(); ++i)
        //     std::cout << "args" << i << ": " << args[i] << "\n";
        execvp(args[0], const_cast<char**>(args));
        // If execvp() fails, this block will be executed
        delete[] args; // Free the array itself
        std::cerr << "[ERROR] Failed to execute command." << std::endl;
        exit(1);
    } else { // Parent process
        close(pipefd[1]); // Close unused write end

        char buffer[256];
        ssize_t bytes, bytesRead;
        while ((bytesRead = read(pipefd[0], buffer, sizeof(buffer))) > 0) {
            // Process and print the data read from the command's output
            // std::cout.write(buffer, bytesRead);
            bytes = bytesRead;
        }
        result = std::string(buffer, bytes); // avoid garbage data due to the lack of initialization

        close(pipefd[0]);
        waitpid(pid, nullptr, 0); // Wait for the child process to finish
    }
    return result;
}

std::string AUTOQ::Util::print_duration(const std::chrono::steady_clock::duration &tp) {
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
        ss << d.count() << 'd' << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}