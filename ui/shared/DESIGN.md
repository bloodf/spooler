# Orca plugin family — shared Vue visual system

Mode: Operate. Vue 3 + PrimeVue 4, one custom Aura preset and one palette for Calculator, Spooler, U1 Control and Organizer. Preserve the user decisions: separate Calculator, integrated stock/printer working area, direct Organizer access. Automatic tab hiding remains limited by the host; styling cannot solve that API boundary.

Typography: system sans, body 14 px, secondary 12 px, section titles 16 px, page title 20 px, primary result 28 px. Monospace only for paths/code/identifiers; tabular numbers for quantities and costs. Spacing 4/8/12/16/24/32 px. Controls 6 px radius; real task panels 12 px. Icons are consistent SVG with textual or accessible labels, not emoji standing in for physical controls. Filament swatches and toolhead colors retain their meaning.

Solid surfaces and a restrained teal accent. Use `palette.json` and the preset, never independent color values per plugin. The host chooses light/dark; tokens provide measured foreground/background pairs for that mode. No ornamental gradients, glass, excessive shadows or entry effects. Domain layout can differ; identical controls and state semantics must look the same.

Use PrimeVue Button/InputText/InputNumber/Select/Checkbox for controls, Message for visible status/error, Dialog for protected decisions, DataTable or semantic rows for data, Tabs for task navigation and ProgressBar for known progress. Add a wrapper only when there is a real shared behavior; do not wrap every component. SVG icons can use PrimeVue slots. No external font/icon download at runtime.

Headers wrap secondary information before hiding primary labels. Keep the active task visible at zoom. Disabled actions explain why; pending commands show what is awaiting confirmation; errors persist with recovery. Blank numbers are not zero. Stale data carries source/age. Uncertain printer/consumption outcomes never appear successful. Keyboard focus survives data refresh and dialogs. PrimeVue supplies primitives, not application-specific safety or correctness.

The product needs clear task composition: selection/context, main work, result/next action. A camera that is off should not displace printer status. Stock remains scannable. Incomplete quotes identify the missing information next to the total. Organizer exposes Arrumar/Preencher directly and preserves the original project.

Acceptance: compare actual built Vue pages across all four plugins in light/dark, 1280/720 px, 200% zoom, long pt-BR/en labels and empty/loading/error/offline/stale/pending states. Cover secondary settings/setup/dock surfaces. Compare computed fonts/radii/palette/controls, not only imported dependencies. Inspect screenshots marked MOCK and exercise keyboard/behavior locally; Orca/WebView/device validation remains pending with Heitor.

Use a common source manifest and enforce it in each build/check. Include licenses, embed every runtime asset, and preserve functional/security/accessibility gates. A framework dependency alone does not complete the migration or guarantee visual quality.
