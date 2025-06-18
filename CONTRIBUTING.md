# Contributing to Braidpool

Contributing to open source is one of the best things you can do. It not only benefits you but many others and projects like Braidpool, which aims to solve one of the critical problems in Bitcoin about centralisation; this becomes even more important. Braidpool is a pure open-source project, meaning anyone can run, modify and use this implementation in its own way. Braidpool is designed to remove centralisation of mining pools and provides a way to overcome this issue.
<br/> <br>
With this responsibility, we also want to put the right efforts into development so everything goes smoothly and in a collaborative way. For this, there are some guidelines designed that will help us to work together so we can read, write and understand each other's code in an efficient way.

## Initials

We deeply value each and every contributions made to Braidpool, we take this as a huge step to make Bitcoin safer and sustainable in future. So, new contributors are always needed and appreciated. <br><br>
Before moving further it's best to familiarize yourself with the Braidpool codebase structure for more information you can refer to 

[overview](https://github.com/braidpool/braidpool/blob/main/docs/overview.md), [specification](https://github.com/braidpool/braidpool/blob/main/docs/braidpool_spec.md), 
and [consensus](https://github.com/braidpool/braidpool/blob/main/docs/braid_consensus.md). This will give you a brief idea about working and its implementation. Braidpool is implemented using Rust, so some familiarity with Rust is also required. The general idea to understand a project is looking into their `tests` directory; the same applies here.

## Structuring a Pull Request

This covers how you should approach a PR from creating to merging. 

+ Use a concise title that summarizes the change, prefixed by the affected area (e.g., `bead`, `dag`, `rpc`, `doc`, `test`, `feat`, `style`) <br>
 ``` e.g., bead: Add dynamic difficulty validation. ```
+ Explain what the PR does and why it’s needed and reference related issues `(e.g., Fixes #123)` or discussions `(e.g., Discord thread)`.
+ Limit the PR to a single feature, bug fix, or refactor. Avoid combining unrelated changes. If ignored, this will lead to several other problems. e.g., hard to review, delay feedback, may block others work.
+ Ensure each commit represents a single logical change (e.g., one commit for adding a function, another for tests) to maintain a clean history, make code reviews easier, and allow for efficient debugging or reverting specific changes if needed.
+ Before merging, squash related commits into one; multiple commits for a single logical change seem irrelevant.

  ```sh
  git rebase -i HEAD~3
  # Squash three commits into one with message:
  bead: Add dynamic difficulty validation

  Implement `validate_difficulty` in `src/bead.rs` to check bead hashes.
  Add unit tests in `tests/bead_validation.rs`. Fixes #123.
  ```
+ For significant changes open a GitHub issue or discuss on Discord (Braidpool [Discord](https://discord.gg/pZYUDwkpPv) ) to confirm alignment with maintainers.
+ Add labels in GitHub according to the PR changes. This will help to understand the current progress and type of the PR.
+ Be sure to run `npx prettier --write .` before commiting so as to cross-check that the commits adhere to the linting scheme of the project's frontend

## PR Review Process

Reviewing is the most beneficial and needed part for any software; thus, we need to ensure thorough evaluation, clear feedback, and efficient collaboration. A reviewer can express their final decision by commenting on the PR discussion page by acknowledging or denying the changes, or the reviewer can also request some changes. Now it's in the author's hands to weigh the opinion of a reviewer by looking at their understanding of the codebase and in the community.  <br>

Here are few steps you can follow while reviewing PRs. 

1. Pull the PR with the respective branch and then build it.

  ```sh
  git fetch origin pull/123/head:pr-123
  git checkout pr-123
  ```
2. Run and see if the codebase is giving you the correct results according to the desired changes. For example, if a PR introduces a new test that will stop Braidpool node after passing a specific argument, then check if it's working in the same way as stated by the PR author. Or a change that introduces a new feature is giving the new results that correspond to that.
3. If it's working fine, then manually review each line of code and think about why that particular line is removed or added in the codebase. And try to find out possible consequences that can occur with that change (always try to find a bug in the new or existing code; think like there is something wrong in the code).
4. Now if you find anything wrong or you can't be able to understand much about that change, then you can ask that thing directly to the PR author via a simple comment. (First try to understand yourself and don't ask silly questions.)
5. Finally, you can publish your official review in GitHub.

## Communication Channels

  For all the other queries, or if you're stuck somewhere while working, or you want to communicate with the community, you can join the [Discord](https://discord.gg/pZYUDwkpPv) channel.
