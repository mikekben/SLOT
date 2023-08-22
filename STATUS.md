# Artifact Evaluation Status

We respectfully request review for the following badges: **Available**, **Evaluated - Functional**, and ****Evaluated - Reusable**.

# Available

Our artifact, SLOT, is made publicly available on Github at https://github.com/mikekben/SLOT. We have created a tag "FSE2023" marking the record version of our artifact for review. We distribute SLOT under the open source GNU General Public License v3.0. The implementation of SLOT and the data collected are therefore publicly accessible. 

# Evaluated-Functional

We provide in three forms substantial documentation of SLOT. First, we provide both the README and INSTALL files included in this repository, which describe in detail how to (1) run a minimal example to show SLOT can be built and functions, (2) re-run large scale experiments on benchmark sets using SLOT, and (3) re-analyze the raw data we collected during our experiments. Second, we provide extensive in-code comments in SLOT's source code to aid future researchers who wish to examine the artifact. Third, we document SLOT in our accepted paper, giving details on design decisions and experimental runs. SLOT's implementation is consistent with each of these descriptions. It is a single complete software artifact which can be re-run. Evidence for this is provided by the implementation, installation packages, and raw data provided in this repository.

# Evaluated-Reusable

In addition to the functionality described above, SLOT is carefully-documented and logically structured. In particular, C++ conventions are adhered-to to make the production of derivative software easier, and SLOT's source code provides copious comments explaining non-obvious functionality. SLOT takes as input constraints in the standard, widely-used, and well-documented SMT-LIB format, and produces output in the same format. Moreover, it's intermediate products (the unoptimized and optimized LLVM IR) are made available to facilitate further scrutiny, and they are in the widely-known language LLVM IR. 
