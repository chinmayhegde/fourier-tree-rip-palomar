# Publishing to GitHub and submitting to Palomar

1. At https://github.com/new create **chinmayhegde/fourier-tree-rip-palomar**,
   select **Private**, and do **not** initialize with README, .gitignore or license.
2. Unzip this package and, in the unzipped `fourier-tree-rip-palomar` directory, run:

```bash
git init -b main
git add .
git commit -m "Prepare Palomar Fourier tree-RIP formalization"
git remote add origin git@github.com:chinmayhegde/fourier-tree-rip-palomar.git
git push -u origin main
```

(Use `https://github.com/chinmayhegde/fourier-tree-rip-palomar.git`
instead if you use HTTPS Git credentials.)

3. Check GitHub **Actions** for both jobs. Do not submit on a red or untested build.
4. Once the check on the chosen commit passes, change the repository to **Public**
   (Settings > General > Danger Zone > Change repository visibility). Palomar
   explicitly cannot fetch a private repo.
5. Retrieve `git rev-parse HEAD` (40 hexadecimal characters) and submit the public
   repository + SHA to https://submit.palomar-registry.org/ . The form requires
   a GitHub sign-in to establish write access. Save the unique status-page URL.

**Important:** the uploaded proof was reported as passing Comparator in its old
pre-module-system form. This package ports it to the mandated `module` system;
its new bytes are not yet proven to pass a Lean build. GitHub Actions must
establish that before submitting. If Lean raises module visibility errors,
make necessary changes, commit and push a new revision, and wait for green CI.

The README and `formalization.yaml` describe known differences from the note;
these are disclosed, not hidden.
