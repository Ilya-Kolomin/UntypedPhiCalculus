# Phi-calculus Implementation in Agda

This is diploma project on implementing the phi-calculus in Agda language, where we define the main construct and prove its confluence.

## Getting Started

This project is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break this implementation, so using older or newer versions usually causes problems.

There are several versions of Agda and its standard library online. If you are using a package manager, like Homebrew or Debian apt, the version of Agda available there may be out of date. Furthermore, Agda is under active development, so if you install the development version from the GitHub, you might find the developers have introduced changes which break the code here. Therefore, it’s important to have the specific versions of Agda and the standard library shown above.

### On macOS: Install the XCode Command Line Tools

On macOS, you’ll need to install [The XCode Command Line Tools][xcode]. For most versions of macOS, you can install these by running the following command:

```bash
xcode-select --install
```

### Install Git

You can check whether you have Git by running the following command:

```bash
git --version
```

If you do not have Git, see [the Git downloads page][git].

### Install GHC and Cabal

Agda is written in Haskell, so to install it we’ll need the _Glorious Haskell Compiler_ and its package manager _Cabal_. This project should work with any version of GHC >=8.10, but is tested with versions 8.10 and 9.2. We recommend installing GHC and Cabal using [ghcup][ghcup].  For instance, once `ghcup` is installed, by typing

```bash
ghcup install ghc 9.2.4
ghcup install cabal recommended

ghcup set ghc 9.2.4
ghcup set cabal recommended
```
or using `ghcup tui` and choosing to `set` the appropriate tools.

> Alternative option: you could install agda directly via `brew install agda` without cobol or ghc. Current version in homebrew is 2.6.3, however, it may change in the future, so that be aware of compatability.

### Install Agda

The easiest way to install Agda is using Cabal. This project uses Agda version 2.6.3. Run the following command:

```bash
cabal update
cabal install Agda-2.6.3
```

This step will take a long time and a lot of memory to complete.

If you have problems or for alternatives see the [Agda installation instructions][agda-readthedocs-installation].

If you'd like, you can [test to see if you've installed Agda correctly][agda-readthedocs-hello-world].

### Install the Agda standard library

We recommend installing this project from Github into your home directory, by running the following command:

```bash
git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/Ilya-Kolomin/UntypedPhiCalculus.git
```

This implementation ships with the required version of the Agda standard library, so if you cloned with the `--recurse-submodules` flag, you’ve already got it, in the `agda-stdlib` directory!

Finally, we need to let Agda know where to find the Agda standard library. Two configuration files are required, one which lists paths to the libraries and one which specifies which libraries to load by default.

On macOS and Unix, if UntypedPhiCalculus is installed in your home directory and you have no existing library configuration files you wish to preserve, run the following commands:

```bash
mkdir -p ~/.agda
echo "$HOME/UntypedPhiCalculus/agda-stdlib/standard-library.agda-lib" >> ~/.agda/libraries
echo "standard-library" >> ~/.agda/defaults
```

This provides access to the Agda standard library.

Otherwise, you will need to edit the appropriate files. Both configuration files are located in the directory `AGDA_DIR`. On UNIX and macOS, `AGDA_DIR` defaults to `~/.agda`. On Windows, `AGDA_DIR` usually defaults to `%AppData%\agda`, where `%AppData%` usually defaults to `C:\Users\USERNAME\AppData\Roaming`.

- If the `AGDA_DIR` directory does not already exist, create it.
- In `AGDA_DIR`, create a plain-text file called `libraries` containing `AGDA_STDLIB/standard-library.agda-lib`, where `AGDA_STDLIB` is the path to where the Agda standard library is located (e.g., `~/UntypedPhiCalculus/agda-stdlib/`). This lets Agda know that an Agda library called `standard-library` is available.
- In `AGDA_DIR`, create a plain-text file called `defaults` containing _just_ the line `standard-library`.

More information about placing the standard libraries is available from [the Library Management page][agda-readthedocs-package-system] of the Agda documentation.

## Setting up an editor for Agda

### Visual Studio Code

[Visual Studio Code][vscode] is a free source code editor developed by Microsoft. There is [a plugin for Agda support][vscode-agda] available on the Visual Studio Marketplace.

<!-- Links -->

[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.3.
[agda-stdlib-version-svg]: https://img.shields.io/badge/agda--stdlib-v1.7.2-blue.svg
[agda-stdlib-version-url]: https://github.com/agda/agda-stdlib/releases/tag/v1.7.2
[ghcup]: https://www.haskell.org/ghcup/
[git]: https://git-scm.com/downloads
[xcode]: https://developer.apple.com/xcode/
[agda-readthedocs-installation]: https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html
[agda-readthedocs-hello-world]: https://agda.readthedocs.io/en/v2.6.3/getting-started/hello-world.html
[agda-readthedocs-holes]: https://agda.readthedocs.io/en/v2.6.3/getting-started/a-taste-of-agda.html#preliminaries
[agda-readthedocs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html
[agda-readthedocs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html#notation-for-key-combinations
[agda-readthedocs-package-system]: https://agda.readthedocs.io/en/v2.6.3/tools/package-system.html#example-using-the-standard-library
[emacs]: https://www.gnu.org/software/emacs/download.html
[emacs-tour]: https://www.gnu.org/software/emacs/tour/
[emacs-home]: https://www.gnu.org/software/emacs/manual/html_node/efaq-w32/Location-of-init-file.html
[aquamacs]: https://aquamacs.org/
[spacemacs]: https://www.spacemacs.org/
[spacemacs-agda]: https://develop.spacemacs.org/layers/+lang/agda/README.html
[vscode]: https://code.visualstudio.com/
[vscode-agda]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[font-sourcecodepro]: https://github.com/adobe-fonts/source-code-pro
[font-dejavusansmono]: https://dejavu-fonts.github.io/
[font-freemono]: https://www.gnu.org/software/freefont/
[font-mononoki]: https://madmalik.github.io/mononoki/
[font-mononoki-debian]: https://packages.debian.org/sid/fonts/fonts-mononoki