cmake_minimum_required(VERSION 3.29)

project(ligraph VERSION 0.1.0 LANGUAGES CXX)

add_library(ligraph STATIC)
add_library(ligraph::ligraph ALIAS ligraph)
target_compile_features(ligraph PUBLIC cxx_std_20)
target_link_libraries(ligraph PUBLIC rstd.alloc)
target_sources(ligraph PUBLIC FILE_SET modules TYPE CXX_MODULES FILES src/lib.cppm)
