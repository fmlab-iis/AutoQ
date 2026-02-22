/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Description:
 *    Test utilities: path helpers and benchmark iteration.
 *
 *****************************************************************************/

#ifndef _AUTOQ_UNIT_TESTS_TEST_UTIL_HH_
#define _AUTOQ_UNIT_TESTS_TEST_UTIL_HH_

#include <filesystem>
#include <functional>
#include <string>

namespace fs = std::filesystem;

/** Maximum benchmark size (subfolder index) to include in iterations. */
constexpr int kMaxBenchmarkSize = 6;

/**
 * Returns the path of a file/directory relative to the current test file.
 * @param file  Typically __FILE__
 * @param rel_path  Relative path from the test file's directory (e.g. "../benchmarks/all/BV/")
 */
inline std::string test_dir_from_file(const char* file, const std::string& rel_path = "") {
    auto base = fs::path(file).parent_path();
    return rel_path.empty() ? base.string() : (base / rel_path).string();
}

/**
 * Iterates benchmark subfolders and calls verify(folder) for each.
 * Skips non-directories and subfolders whose numeric name exceeds max_size.
 */
template<typename F>
void for_each_benchmark_case(const std::string& benchmark_base_path, F&& verify, int max_size = kMaxBenchmarkSize) {
    for (const auto& entry : fs::directory_iterator(benchmark_base_path)) {
        if (!entry.is_directory()) continue;
        const std::string path_str = entry.path().string();
        const std::string name = path_str.substr(path_str.find_last_of('/') + 1);
        int idx = 0;
        try {
            idx = std::stoi(name);
        } catch (...) {
            idx = 0;  // non-numeric names: include (e.g. "10a")
        }
        if (idx > max_size) continue;
        verify(path_str);
    }
}

#endif
