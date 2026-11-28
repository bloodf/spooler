# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""tr(): the Python-worded texts in the page's languages, and number formatting."""

import html
import re
import sys

from . import core as _core


def tr(text: str, /, **values: object) -> str:
    """text in the current language, with its {names} filled in. The English text is the key and what is
    shown when a language has no entry for it."""
    found = _TEXTS.get(_tab.text_language(), {}).get(text, text)
    return found.format(**values) if values else found


def _sentences(parts: list[str]) -> str:
    """Whole sentences in a row: a space between them, none in Chinese."""
    return ("" if _tab.text_language() == "zh-CN" else " ").join(parts)


def fmt_num(value: float, digits: int = 0, group: bool = False) -> str:
    """A number as the current language writes it: 1,234.5 in English and Chinese, 1.234,5 in German,
    Portuguese and Spanish, 12 345,5 in Polish (Spanish and Polish group only from 10,000 up, as the page's
    Intl.NumberFormat does; Polish groups with a no-break space)."""
    language = _tab.text_language()
    if group and not (language in ("es", "pl") and abs(value) < 10000):
        text = f"{value:,.{digits}f}"
    else:
        text = f"{value:.{digits}f}"
    if language in ("pt-BR", "es", "de"):
        text = text.replace(",", "\0").replace(".", ",").replace("\0", ".")
    elif language == "pl":
        text = text.replace(",", "\u00a0").replace(".", ",")
    return text


def fmt_money(amount: float, code: str) -> str:
    """An amount with its currency sign where the language puts it: "€1.23", in German, Spanish and Polish "1,23 €"."""
    sign, text = _stats.CUR_SIGNS.get(code, code + " "), fmt_num(amount, 2)
    return f"{text}\u00a0{sign.strip()}" if _tab.text_language() in ("de", "es", "pl") else sign + text


# Python-worded texts in the page's other languages, by their English text: (pt-BR, es, de, zh-CN, pl). Terms follow
# OrcaSlicer's own translations (Spanish "carrete", "ranura", "perfil"; German "Spule", "Slot", "Profil", formal "Sie";
# Chinese "料盘", "槽位", "预设", "耗材丝", full-width punctuation; Polish "szpula", "slot", "profil", informal "ty").
# Spoolman data (names, vendors, notes) is never translated.
_TEXT_LANGS = ("pt-BR", "es", "de", "zh-CN", "pl")
_TEXT_ROWS: dict[str, tuple[str, str, str, str, str]] = {
    "Spooler could not open its page.": (
        "O Spooler não conseguiu abrir a página.",
        "Spooler no pudo abrir su página.",
        "Spooler konnte seine Seite nicht öffnen.",
        "Spooler 无法打开页面。",
        "Spooler nie mógł otworzyć swojej strony.",
    ),
    "Copy diagnostics": (
        "Copiar diagnóstico",
        "Copiar diagnóstico",
        "Diagnose kopieren",
        "复制诊断信息",
        "Kopiuj diagnostykę",
    ),
    "The log is at {path}.": (
        "O log está em {path}.",
        "El registro está en {path}.",
        "Das Protokoll liegt unter {path}.",
        "日志位于 {path}。",
        "Dziennik jest w {path}.",
    ),
    "Spoolman refused to add the Use with field ({error}); nothing was written.": (
        "O Spoolman recusou adicionar o campo Usar com ({error}); nada foi gravado.",
        "Spoolman rechazó añadir el campo Usar con ({error}); no se guardó nada.",
        "Spoolman hat das Feld Verwenden mit nicht angelegt ({error}); es wurde nichts geschrieben.",
        "Spoolman 拒绝添加“用于”字段（{error}）；未写入任何内容。",
        "Spoolman odmówił dodania pola „Używaj z” ({error}); niczego nie zapisano.",
    ),
    "Signed in ({region})": (
        "Conectado ({region})",
        "Sesión iniciada ({region})",
        "Angemeldet ({region})",
        "已登录（{region}）",
        "Zalogowano ({region})",
    ),
    "Signed in as {user} ({region})": (
        "Conectado como {user} ({region})",
        "Sesión iniciada como {user} ({region})",
        "Angemeldet als {user} ({region})",
        "已登录为 {user}（{region}）",
        "Zalogowano jako {user} ({region})",
    ),
    "Global": (
        "Global",
        "Global",
        "Global",
        "全球",
        "Globalny",
    ),
    "China": (
        "China",
        "China",
        "China",
        "中国",
        "Chiny",
    ),
    "slot {n} ({name})": (
        "slot {n} ({name})",
        "la ranura {n} ({name})",
        "Slot {n} ({name})",
        "槽位 {n}（{name}）",
        "slot {n} ({name})",
    ),
    "slots {n} ({name})": (
        "slots {n} ({name})",
        "las ranuras {n} ({name})",
        "Slots {n} ({name})",
        "槽位 {n}（{name}）",
        "sloty {n} ({name})",
    ),
    "needs {grams} of filament": (
        "precisa de {grams} de filamento",
        "necesita {grams} de filamento",
        "braucht {grams} Filament",
        "需要 {grams} 耗材丝",
        "potrzebuje {grams} filamentu",
    ),
    "need {grams} of filament together": (
        "precisam de {grams} de filamento juntos",
        "necesitan {grams} de filamento en total",
        "brauchen zusammen {grams} Filament",
        "共需要 {grams} 耗材丝",
        "potrzebują łącznie {grams} filamentu",
    ),
    "the spool has {have}": (
        "a bobina tem {have}",
        "el carrete tiene {have}",
        "die Spule hat {have}",
        "料盘有 {have}",
        "szpula ma {have}",
    ),
    "the {count} spools have {have} between them": (
        "as {count} bobinas têm {have} juntas",
        "los {count} carretes tienen {have} en total",
        "die {count} Spulen haben zusammen {have}",
        "这 {count} 个料盘共有 {have}",
        "szpule ({count}) mają łącznie {have}",
    ),
    " (only {matches} of {pool} matching spools are in {source})": (
        " (só {matches} de {pool} bobinas compatíveis estão no {source})",
        " (solo {matches} de {pool} carretes compatibles están en {source})",
        " (nur {matches} von {pool} passenden Spulen sind in {source})",
        "（{pool} 个匹配料盘中只有 {matches} 个在 {source} 中）",
        " ({source} zawiera tylko {matches} z {pool} pasujących szpul)",
    ),
    "slot {n}": (
        "slot {n}",
        "ranura {n}",
        "Slot {n}",
        "槽位 {n}",
        "slot {n}",
    ),
    "slots {n}": (
        "slots {n}",
        "ranuras {n}",
        "Slots {n}",
        "槽位 {n}",
        "sloty {n}",
    ),
    "Slot {n}": (
        "Slot {n}",
        "Ranura {n}",
        "Slot {n}",
        "槽位 {n}",
        "Slot {n}",
    ),
    "Slots {n}": (
        "Slots {n}",
        "Ranuras {n}",
        "Slots {n}",
        "槽位 {n}",
        "Sloty {n}",
    ),
    "{name} ({slots}) has no drying date.": (
        "{name} ({slots}) não tem data de secagem.",
        "{name} ({slots}) no tiene fecha de secado.",
        "{name} ({slots}) hat kein Trocknungsdatum.",
        "{name}（{slots}）没有烘干日期。",
        "{name} ({slots}) nie ma daty suszenia.",
    ),
    "{name} ({slots}) was last dried {days} day ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dia.",
        "{name} ({slots}) se secó por última vez hace {days} día.",
        "{name} ({slots}) wurde zuletzt vor {days} Tag getrocknet.",
        "{name}（{slots}）上次烘干是在 {days} 天前。",
        "{name} ({slots}) suszono ostatnio {days} dzień temu.",
    ),
    "{name} ({slots}) was last dried {days} days ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dias.",
        "{name} ({slots}) se secó por última vez hace {days} días.",
        "{name} ({slots}) wurde zuletzt vor {days} Tagen getrocknet.",
        "{name}（{slots}）上次烘干是在 {days} 天前。",
        "{name} ({slots}) suszono ostatnio {days} dni temu.",
    ),
    "About {cost} of filament.": (
        "Cerca de {cost} de filamento.",
        "Unos {cost} de filamento.",
        "Etwa {cost} an Filament.",
        "耗材丝成本约 {cost}。",
        "Około {cost} za filament.",
    ),
    "Loaded {count} filament slot(s) from the printer. OrcaSlicer doesn't let plugins set slot colours, so a slot keeps its old colour until you pick its filament in the dropdown.": (
        "{count} slot(s) de filamento carregado(s) da impressora. O OrcaSlicer não deixa plugins definirem a cor dos slots, então um slot mantém a cor antiga até você escolher o filamento dele na lista.",
        "Se cargaron {count} ranura(s) de filamento desde la impresora. OrcaSlicer no deja que los plugins cambien el color de las ranuras, así que una ranura conserva su color anterior hasta que eliges su filamento en el desplegable.",
        "{count} Filament-Slot(s) vom Drucker geladen. OrcaSlicer lässt Plugins die Slotfarben nicht ändern, daher behält ein Slot seine alte Farbe, bis Sie sein Filament in der Auswahlliste wählen.",
        "已从打印机载入 {count} 个耗材丝槽位。OrcaSlicer 不允许插件设置槽位颜色，所以在您从下拉列表中选择该槽位的耗材丝之前，槽位会保留原来的颜色。",
        "Wczytano sloty filamentu z drukarki: {count}. OrcaSlicer nie pozwala wtyczkom ustawiać kolorów slotów, więc slot zachowuje dawny kolor, dopóki nie wybierzesz jego filamentu z listy.",
    ),
    " No Spoolman filament matched slot(s) {slots}.": (
        " Nenhum filamento do Spoolman corresponde ao(s) slot(s) {slots}.",
        " Ningún filamento de Spoolman coincide con la(s) ranura(s) {slots}.",
        " Kein Spoolman-Filament passt zu Slot(s) {slots}.",
        "没有 Spoolman 耗材丝与槽位 {slots} 匹配。",
        " Żaden filament ze Spoolmana nie pasował do slotów: {slots}.",
    ),
    " Could not change slot(s) {slots}.": (
        " Não foi possível alterar o(s) slot(s) {slots}.",
        " No se pudo cambiar la(s) ranura(s) {slots}.",
        " Slot(s) {slots} konnte(n) nicht geändert werden.",
        "无法更改槽位 {slots}。",
        " Nie udało się zmienić slotów: {slots}.",
    ),
    "Spooler: {spool} is down to {grams} g": (
        "Spooler: {spool} está com apenas {grams} g",
        "Spooler: quedan {grams} g de {spool}",
        "Spooler: {spool} hat nur noch {grams} g",
        "Spooler：{spool} 只剩 {grams} g",
        "Spooler: {spool} – zostało {grams} g",
    ),
    "Bambu blocked the request (HTTP 403)": (
        "A Bambu bloqueou a solicitação (HTTP 403)",
        "Bambu bloqueó la solicitud (HTTP 403)",
        "Bambu hat die Anfrage blockiert (HTTP 403)",
        "Bambu 拦截了该请求（HTTP 403）",
        "Bambu zablokowało żądanie (HTTP 403)",
    ),
    "Bambu Cloud returned an error (HTTP {code})": (
        "A Bambu Cloud retornou um erro (HTTP {code})",
        "Bambu Cloud devolvió un error (HTTP {code})",
        "Bambu Cloud hat einen Fehler gemeldet (HTTP {code})",
        "Bambu Cloud 返回错误（HTTP {code}）",
        "Bambu Cloud zwróciło błąd (HTTP {code})",
    ),
    "Bambu Cloud didn't sign you in": (
        "A Bambu Cloud não fez seu login",
        "Bambu Cloud no inició tu sesión",
        "Bambu Cloud hat Sie nicht angemeldet",
        "Bambu Cloud 登录失败",
        "Bambu Cloud cię nie zalogowało",
    ),
    "Bambu Cloud didn't accept your sign-in": (
        "A Bambu Cloud não aceitou seu login",
        "Bambu Cloud no aceptó tu inicio de sesión",
        "Bambu Cloud hat Ihre Anmeldung nicht akzeptiert",
        "Bambu Cloud 不接受您的登录",
        "Bambu Cloud nie przyjęło logowania",
    ),
    "Bambu Cloud sent a reply Spooler doesn't understand": (
        "A Bambu Cloud enviou uma resposta que o Spooler não entende",
        "Bambu Cloud envió una respuesta que Spooler no entiende",
        "Bambu Cloud hat eine Antwort gesendet, die Spooler nicht versteht",
        "Bambu Cloud 返回了 Spooler 无法识别的回复",
        "Bambu Cloud wysłało odpowiedź, której Spooler nie rozumie",
    ),
    "Could not reach Bambu Cloud ({reason})": (
        "Não foi possível acessar a Bambu Cloud ({reason})",
        "No se pudo conectar con Bambu Cloud ({reason})",
        "Bambu Cloud ist nicht erreichbar ({reason})",
        "无法连接 Bambu Cloud（{reason}）",
        "Nie można połączyć z Bambu Cloud ({reason})",
    ),
    "Signed in, but Spooler could not save the sign-in to {folder}": (
        "Login feito, mas o Spooler não conseguiu salvá-lo em {folder}",
        "Sesión iniciada, pero Spooler no pudo guardarla en {folder}",
        "Angemeldet, aber Spooler konnte die Anmeldung nicht in {folder} speichern",
        "已登录，但 Spooler 无法将登录信息保存到 {folder}",
        "Zalogowano, ale Spooler nie mógł zapisać logowania w {folder}",
    ),
    "Enter your Bambu email and password": (
        "Digite seu e-mail e senha da Bambu",
        "Introduce tu correo y contraseña de Bambu",
        "Geben Sie Ihre Bambu-E-Mail-Adresse und Ihr Passwort ein",
        "请输入您的 Bambu 邮箱和密码",
        "Wpisz e-mail i hasło do konta Bambu",
    ),
    "Your sign-in timed out. Enter your email and password again": (
        "O login expirou. Digite seu e-mail e senha de novo",
        "El inicio de sesión caducó. Introduce de nuevo tu correo y contraseña",
        "Die Anmeldung ist abgelaufen. Geben Sie E-Mail-Adresse und Passwort erneut ein",
        "登录已超时。请重新输入邮箱和密码",
        "Logowanie wygasło. Wpisz ponownie e-mail i hasło",
    ),
    "Enter your Bambu Lab verification code": (
        "Digite seu código de verificação da Bambu Lab",
        "Introduce tu código de verificación de Bambu Lab",
        "Geben Sie Ihren Bambu Lab-Bestätigungscode ein",
        "请输入您的 Bambu Lab 验证码",
        "Wpisz kod weryfikacyjny Bambu Lab",
    ),
    "Signed out": (
        "Desconectado",
        "Sesión cerrada",
        "Abgemeldet",
        "未登录",
        "Wylogowano",
    ),
    "Sign-in expired": (
        "Login expirado",
        "Sesión caducada",
        "Anmeldung abgelaufen",
        "登录已过期",
        "Logowanie wygasło",
    ),
    "Your Bambu sign-in has expired": (
        "Seu login na Bambu expirou",
        "Tu sesión de Bambu caducó",
        "Ihre Bambu-Anmeldung ist abgelaufen",
        "您的 Bambu 登录已过期",
        "Twoje logowanie do Bambu wygasło",
    ),
    "Your saved Bambu sign-in is unreadable": (
        "Não foi possível ler seu login salvo da Bambu",
        "No se puede leer tu sesión de Bambu guardada",
        "Ihre gespeicherte Bambu-Anmeldung ist nicht lesbar",
        "无法读取已保存的 Bambu 登录信息",
        "Zapisanego logowania do Bambu nie da się odczytać",
    ),
    "Open Settings and sign in to Bambu Cloud.": (
        "Abra os Ajustes e entre na Bambu Cloud.",
        "Abre Ajustes e inicia sesión en Bambu Cloud.",
        "Öffnen Sie die Einstellungen und melden Sie sich bei Bambu Cloud an.",
        "请打开设置并登录 Bambu Cloud。",
        "Otwórz ustawienia i zaloguj się do Bambu Cloud.",
    ),
    "The spool source kept changing while loading; refresh to try again.": (
        "A origem das bobinas mudou durante o carregamento; atualize para tentar de novo.",
        "El origen de los carretes cambió mientras se cargaba; actualiza para intentarlo de nuevo.",
        "Die Spulenquelle hat sich beim Laden mehrmals geändert; aktualisieren Sie, um es erneut zu versuchen.",
        "加载时料盘来源一直在变化；请刷新后重试。",
        "Źródło szpul zmieniało się podczas wczytywania; odśwież, aby spróbować ponownie.",
    ),
    "{printer} now books its usage to spool #{id}.": (
        "{printer} agora registra o consumo na bobina #{id}.",
        "{printer} ahora registra su consumo en el carrete #{id}.",
        "{printer} bucht den Verbrauch jetzt auf Spule #{id}.",
        "{printer} 现在将用量记到料盘 #{id}。",
        "{printer} księguje teraz zużycie na szpulę #{id}.",
    ),
    "Spoolman refused it (HTTP {code})": (
        "O Spoolman recusou (HTTP {code})",
        "Spoolman lo rechazó (HTTP {code})",
        "Spoolman hat abgelehnt (HTTP {code})",
        "Spoolman 拒绝了该请求（HTTP {code}）",
        "Spoolman odrzucił to (HTTP {code})",
    ),
    "Could not reach Spoolman ({reason})": (
        "Não foi possível acessar o Spoolman ({reason})",
        "No se pudo conectar con Spoolman ({reason})",
        "Spoolman ist nicht erreichbar ({reason})",
        "无法连接 Spoolman（{reason}）",
        "Nie można połączyć ze Spoolmanem ({reason})",
    ),
    "Could not reach Spoolman at {url} ({reason})": (
        "Não foi possível acessar o Spoolman em {url} ({reason})",
        "No se pudo conectar con Spoolman en {url} ({reason})",
        "Spoolman unter {url} ist nicht erreichbar ({reason})",
        "无法连接位于 {url} 的 Spoolman（{reason}）",
        "Nie można połączyć ze Spoolmanem pod adresem {url} ({reason})",
    ),
    "Spooler couldn't read Spoolman's version, so it can't tell whether changing the dried date would erase this spool's other extra fields. Nothing was written; check the connection and try again.": (
        "O Spooler não conseguiu ler a versão do Spoolman, então não sabe se alterar a data de secagem apagaria os outros campos extras desta bobina. Nada foi gravado; confira a conexão e tente de novo.",
        "Spooler no pudo leer la versión de Spoolman, así que no sabe si cambiar la fecha de secado borraría los demás campos extra de este carrete. No se escribió nada; revisa la conexión e inténtalo de nuevo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, ob das Ändern des Trocknungsdatums die anderen Zusatzfelder dieser Spule löschen würde. Es wurde nichts geschrieben; prüfen Sie die Verbindung und versuchen Sie es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法确定更改烘干日期是否会清除此料盘的其他额外字段。未写入任何内容；请检查连接后重试。",
        "Spooler nie mógł odczytać wersji Spoolmana, więc nie wie, czy zmiana daty suszenia nie skasuje pozostałych dodatkowych pól tej szpuli. Niczego nie zapisano; sprawdź połączenie i spróbuj ponownie.",
    ),
    "Spooler couldn't read this spool's extra fields, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras desta bobina, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra de este carrete, y esta versión de Spoolman los reemplaza todos en cada cambio. No se escribió nada.",
        "Spooler konnte die Zusatzfelder dieser Spule nicht lesen, und diese Spoolman-Version ersetzt bei jeder Änderung alle. Es wurde nichts geschrieben.",
        "Spooler 无法读取此料盘的额外字段，而此版本的 Spoolman 每次更改都会替换全部字段。未写入任何内容。",
        "Spooler nie mógł odczytać dodatkowych pól tej szpuli, a ta wersja Spoolmana przy zmianie zastępuje je wszystkie. Niczego nie zapisano.",
    ),
    "Could not open {url}.": (
        "Não foi possível abrir {url}.",
        "No se pudo abrir {url}.",
        "{url} konnte nicht geöffnet werden.",
        "无法打开 {url}。",
        "Nie można otworzyć {url}.",
    ),
    "Saved {path}": (
        "Salvo em {path}",
        "Guardado en {path}",
        "Gespeichert: {path}",
        "已保存到 {path}",
        "Zapisano {path}",
    ),
    "No web browser could be launched. Open this address yourself:\n{url}": (
        "Nenhum navegador pôde ser aberto. Abra este endereço você mesmo:\n{url}",
        "No se pudo abrir ningún navegador. Abre esta dirección tú mismo:\n{url}",
        "Es konnte kein Webbrowser gestartet werden. Öffnen Sie diese Adresse selbst:\n{url}",
        "无法启动网页浏览器。请自行打开此地址：\n{url}",
        "Nie udało się uruchomić przeglądarki. Otwórz ten adres samodzielnie:\n{url}",
    ),
    "Could not open the browser: {error}": (
        "Não foi possível abrir o navegador: {error}",
        "No se pudo abrir el navegador: {error}",
        "Der Browser konnte nicht geöffnet werden: {error}",
        "无法打开浏览器：{error}",
        "Nie można otworzyć przeglądarki: {error}",
    ),
    ".": (
        ".",
        ".",
        ".",
        "。",
        ".",
    ),
    ", ": (
        ", ",
        ", ",
        ", ",
        "、",
        ", ",
    ),
    " and ": (
        " e ",
        " y ",
        " und ",
        " 和 ",
        " i ",
    ),
    "Spooler: {text}": (
        "Spooler: {text}",
        "Spooler: {text}",
        "Spooler: {text}",
        "Spooler：{text}",
        "Spooler: {text}",
    ),
    " (+{count} more, see the log)": (
        " (+{count}, veja o log)",
        " (+{count} más, consulta el registro)",
        " (+{count} weitere, siehe Protokoll)",
        "（另有 {count} 条，见日志）",
        " (+{count} więcej, szczegóły w logu)",
    ),
    "the address must start with http:// or https://": (
        "o endereço deve começar com http:// ou https://",
        "la dirección debe empezar por http:// o https://",
        "die Adresse muss mit http:// oder https:// beginnen",
        "地址必须以 http:// 或 https:// 开头",
        "adres musi zaczynać się od http:// lub https://",
    ),
    "No Spoolman URL configured yet": (
        "Nenhuma URL do Spoolman configurada ainda",
        "Aún no hay una URL de Spoolman configurada",
        "Noch keine Spoolman-URL eingerichtet",
        "尚未配置 Spoolman URL",
        "Nie skonfigurowano jeszcze adresu URL Spoolmana",
    ),
    "No Spoolman URL configured yet - click Settings to set one.": (
        "Nenhuma URL do Spoolman configurada ainda: clique em Ajustes para definir uma.",
        "Aún no hay una URL de Spoolman configurada: pulsa Ajustes para añadirla.",
        "Noch keine Spoolman-URL eingerichtet: Klicken Sie auf Einstellungen, um eine festzulegen.",
        "尚未配置 Spoolman URL：请点击设置进行配置。",
        "Nie skonfigurowano jeszcze adresu URL Spoolmana – kliknij Ustawienia, aby go podać.",
    ),
    "{url} answered, but not like Spoolman does": (
        "{url} respondeu, mas não como o Spoolman responde",
        "{url} respondió, pero no como lo hace Spoolman",
        "{url} hat geantwortet, aber nicht wie Spoolman",
        "{url} 有响应，但不像 Spoolman 的响应",
        "{url} odpowiedział, ale nie tak jak Spoolman",
    ),
    "No OrcaSlicer user folder accepted the presets": (
        "Nenhuma pasta de usuário do OrcaSlicer aceitou os perfis",
        "Ninguna carpeta de usuario de OrcaSlicer aceptó los perfiles",
        "Kein OrcaSlicer-Benutzerordner hat die Profile angenommen",
        "没有 OrcaSlicer 用户文件夹接受这些预设",
        "Żaden folder użytkownika OrcaSlicer nie przyjął profili",
    ),
    "The spool source changed in Settings while this ran, so Spooler stopped before writing anything more. Try again.": (
        "A origem das bobinas mudou nos Ajustes durante a execução, então o Spooler parou antes de gravar mais nada. Tente de novo.",
        "El origen de los carretes cambió en Ajustes mientras esto se ejecutaba, así que Spooler se detuvo antes de escribir nada más. Inténtalo de nuevo.",
        "Die Spulenquelle wurde während des Vorgangs in den Einstellungen geändert, daher hat Spooler angehalten, bevor weiteres geschrieben wurde. Versuchen Sie es erneut.",
        "运行期间设置中的料盘来源发生了变化，Spooler 已停止，未再写入任何内容。请重试。",
        "Źródło szpul zmieniło się w ustawieniach w trakcie działania, więc Spooler przerwał przed dalszym zapisem. Spróbuj ponownie.",
    ),
    "Spoolman is not the spool source.": (
        "O Spoolman não é a origem das bobinas.",
        "Spoolman no es el origen de los carretes.",
        "Spoolman ist nicht die Spulenquelle.",
        "Spoolman 不是料盘来源。",
        "Spoolman nie jest źródłem szpul.",
    ),
    "Open a Spooler preset in OrcaSlicer's filament settings and change it first.": (
        "Primeiro abra um perfil do Spooler nos ajustes de filamento do OrcaSlicer e altere-o.",
        "Primero abre un perfil de Spooler en los ajustes de filamento de OrcaSlicer y cámbialo.",
        "Öffnen Sie zuerst ein Spooler-Profil in den Filamenteinstellungen von OrcaSlicer und ändern Sie es.",
        "请先在 OrcaSlicer 的耗材丝设置中打开一个 Spooler 预设并修改它。",
        "Najpierw otwórz profil Spoolera w ustawieniach filamentu OrcaSlicer i go zmień.",
    ),
    'Spoolman refused to add the OrcaSlicer preset field ({error}); nothing was written.': (
        'O Spoolman recusou adicionar o campo Perfil do OrcaSlicer ({error}); nada foi gravado.',
        'Spoolman rechazó añadir el campo Perfil de OrcaSlicer ({error}); no se escribió nada.',
        'Spoolman hat das Feld OrcaSlicer-Profil nicht angelegt ({error}); nichts wurde geschrieben.',
        'Spoolman 拒绝添加 OrcaSlicer 预设字段（{error}）；未写入任何内容。',
        'Spoolman odmówił dodania pola Profil OrcaSlicer ({error}); nic nie zapisano.',
    ),
    "That preset is no longer one of this spool's. Refresh, then send it again.": (
        'Esse perfil não é mais um desta bobina. Atualize e envie de novo.',
        'Ese perfil ya no es de esta bobina. Actualiza y vuelve a enviarlo.',
        'Dieses Profil gehört nicht mehr zu dieser Spule. Aktualisiere und sende es erneut.',
        '该预设已不属于这个料盘。请刷新后重新发送。',
        'Ten profil nie należy już do tej szpuli. Odśwież i wyślij ponownie.',
    ),
    'Select a printer in OrcaSlicer first, then send again.': (
        'Selecione primeiro uma impressora no OrcaSlicer e envie de novo.',
        'Selecciona primero una impresora en OrcaSlicer y vuelve a enviar.',
        'Wähle zuerst einen Drucker in OrcaSlicer aus und sende dann erneut.',
        '请先在 OrcaSlicer 中选择打印机，然后重新发送。',
        'Najpierw wybierz drukarkę w OrcaSlicer, a potem wyślij ponownie.',
    ),
    "{name} can't be compared with a Spooler preset for this printer; nothing was sent.": (
        '{name} não pode ser comparado com um perfil do Spooler para esta impressora; nada foi enviado.',
        '{name} no se puede comparar con un perfil de Spooler para esta impresora; no se envió nada.',
        '{name} lässt sich mit keinem Spooler-Profil für diesen Drucker vergleichen; nichts wurde gesendet.',
        '无法将 {name} 与此打印机的 Spooler 预设进行比较；未发送任何内容。',
        'Nie można porównać {name} z profilem Spoolera dla tej drukarki; nic nie wysłano.',
    ),
    '{name} has no unsaved changes, and its saved settings match Spoolman: nothing to send.': (
        '{name} não tem alterações não salvas, e os ajustes salvos batem com o Spoolman: nada a enviar.',
        '{name} no tiene cambios sin guardar y sus ajustes guardados coinciden con Spoolman: nada que enviar.',
        '{name} hat keine ungespeicherten Änderungen, und die gespeicherten Einstellungen stimmen mit Spoolman überein: nichts zu senden.',
        '{name} 没有未保存的更改，且已保存的设置与 Spoolman 一致：无需发送。',
        '{name} nie ma niezapisanych zmian, a zapisane ustawienia zgadzają się ze Spoolmanem: nie ma czego wysłać.',
    ),
    '{name} is linked to this spool only, and Spoolman keeps settings on the filament every spool of it shares; nothing was sent. Save your changes in the preset itself, or link the filament instead.': (
        '{name} está vinculado só a esta bobina, e o Spoolman guarda os ajustes no filamento que todas as bobinas dele compartilham; nada foi enviado. Salve as alterações no próprio perfil, ou vincule o filamento.',
        '{name} está vinculado solo a este carrete, y Spoolman guarda los ajustes en el filamento que comparten todos sus carretes; no se envió nada. Guarda los cambios en el propio perfil, o vincula el filamento.',
        '{name} ist nur mit dieser Spule verknüpft, und Spoolman speichert Einstellungen am Filament, das alle seine Spulen teilen; nichts wurde gesendet. Speichere die Änderungen im Profil selbst oder verknüpfe stattdessen das Filament.',
        '{name} 仅关联到此料盘，而 Spoolman 将设置保存在其所有料盘共用的耗材丝上；未发送任何内容。请在预设本身中保存更改，或改为关联耗材丝。',
        '{name} jest powiązany tylko z tą szpulą, a Spoolman trzyma ustawienia w filamencie wspólnym dla wszystkich jego szpul; nic nie wysłano. Zapisz zmiany w samym profilu albo powiąż filament.',
    ),
    "{name} has no unsaved changes to send.": (
        "{name} não tem alterações não salvas para enviar.",
        "{name} no tiene cambios sin guardar que enviar.",
        "{name} hat keine ungespeicherten Änderungen zum Senden.",
        "{name} 没有可发送的未保存更改。",
        "{name} nie ma niezapisanych zmian do wysłania.",
    ),
    "{name} is no longer a Spooler preset. Refresh, then send it again.": (
        "{name} não é mais um perfil do Spooler. Atualize e envie de novo.",
        "{name} ya no es un perfil de Spooler. Actualiza y vuelve a enviarlo.",
        "{name} ist kein Spooler-Profil mehr. Aktualisieren Sie und senden Sie es erneut.",
        "{name} 已不再是 Spooler 预设。请刷新后重新发送。",
        "{name} nie jest już profilem Spoolera. Odśwież, a potem wyślij ponownie.",
    ),
    "The {field} field of {name}'s filament isn't a JSON object; fix it in Spoolman, then send again.": (
        "O campo {field} do filamento de {name} não é um objeto JSON; corrija-o no Spoolman e envie de novo.",
        "El campo {field} del filamento de {name} no es un objeto JSON; corrígelo en Spoolman y vuelve a enviarlo.",
        "Das Feld {field} des Filaments von {name} ist kein JSON-Objekt; korrigieren Sie es in Spoolman und senden Sie erneut.",
        "{name} 的耗材丝的 {field} 字段不是 JSON 对象；请在 Spoolman 中修正后重新发送。",
        "Pole {field} filamentu {name} nie jest obiektem JSON; popraw je w Spoolmanie, a potem wyślij ponownie.",
    ),
    "The {field} field of {name}'s filament changed in Spoolman and isn't a JSON object now; fix it in Spoolman, then send again.": (
        "O campo {field} do filamento de {name} mudou no Spoolman e agora não é um objeto JSON; corrija-o no Spoolman e envie de novo.",
        "El campo {field} del filamento de {name} cambió en Spoolman y ahora no es un objeto JSON; corrígelo en Spoolman y vuelve a enviarlo.",
        "Das Feld {field} des Filaments von {name} wurde in Spoolman geändert und ist jetzt kein JSON-Objekt; korrigieren Sie es in Spoolman und senden Sie erneut.",
        "{name} 的耗材丝的 {field} 字段已在 Spoolman 中更改，现在不是 JSON 对象；请在 Spoolman 中修正后重新发送。",
        "Pole {field} filamentu {name} zmieniło się w Spoolmanie i nie jest już obiektem JSON; popraw je w Spoolmanie, a potem wyślij ponownie.",
    ),
    "Spooler: {name} has new calibrated values. Open Spooler to save them to Spoolman or skip them.": (
        "Spooler: {name} tem novos valores de calibração. Abra o Spooler para salvá-los no Spoolman ou ignorá-los.",
        "Spooler: {name} tiene nuevos valores de calibración. Abre Spooler para guardarlos en Spoolman u omitirlos.",
        "Spooler: {name} hat neue Kalibrierungswerte. Öffnen Sie Spooler, um sie in Spoolman zu speichern oder zu überspringen.",
        "Spooler：{name} 有新的校准值。打开 Spooler 将其保存到 Spoolman，或跳过。",
        "Spooler: {name} ma nowe skalibrowane wartości. Otwórz Spooler, aby zapisać je w Spoolmanie albo pominąć.",
    ),
    "Sent {settings} to Spoolman for {name}.": (
        "{settings} enviado(s) ao Spoolman para {name}.",
        "Se envió {settings} a Spoolman para {name}.",
        "{settings} für {name} an Spoolman gesendet.",
        "已将 {name} 的 {settings} 发送到 Spoolman。",
        "Wysłano do Spoolmana: {settings} dla {name}.",
    ),
    "Kept Spoolman's newer value for {settings}: the preset now has it, and your change stays unsaved; send again to use yours, or discard it.": (
        "Mantido o valor mais recente do Spoolman para {settings}: o perfil agora tem esse valor e sua alteração continua não salva; envie de novo para usar a sua ou descarte-a.",
        "Se mantuvo el valor más reciente de Spoolman para {settings}: el perfil ya lo tiene y tu cambio sigue sin guardar; vuelve a enviarlo para usar el tuyo o descártalo.",
        "Der neuere Spoolman-Wert für {settings} wurde behalten: Das Profil hat ihn jetzt, und Ihre Änderung bleibt ungespeichert; senden Sie erneut, um Ihren Wert zu verwenden, oder verwerfen Sie ihn.",
        "已保留 Spoolman 中 {settings} 的较新值：预设现在使用该值，您的更改仍未保存；再次发送可使用您的值，或将其放弃。",
        "Zachowano nowszą wartość ze Spoolmana dla: {settings}. Profil ma ją teraz, a twoja zmiana pozostaje niezapisana; wyślij ponownie, aby użyć swojej, albo ją odrzuć.",
    ),
    "Not sent: {settings}. Spoolman's {field} field holds only calibration settings; colour, vendor, material and name come from its own fields.": (
        "Não enviado: {settings}. O campo {field} do Spoolman guarda só ajustes de calibração; cor, fabricante, material e nome vêm dos campos próprios dele.",
        "No enviado: {settings}. El campo {field} de Spoolman solo guarda ajustes de calibración; el color, el fabricante, el material y el nombre vienen de sus propios campos.",
        "Nicht gesendet: {settings}. Das Spoolman-Feld {field} enthält nur Kalibrierungseinstellungen; Farbe, Hersteller, Material und Name stammen aus eigenen Feldern.",
        "未发送：{settings}。Spoolman 的 {field} 字段只保存校准设置；颜色、供应商、材料和名称来自其各自的字段。",
        "Nie wysłano: {settings}. Pole {field} w Spoolmanie przechowuje tylko ustawienia kalibracji; kolor, producent, materiał i nazwa pochodzą z jego własnych pól.",
    ),
    "The presets were not rebuilt: {error}": (
        "Os perfis não foram recriados: {error}",
        "Los perfiles no se reconstruyeron: {error}",
        "Die Profile wurden nicht neu erstellt: {error}",
        "预设未重建：{error}",
        "Nie przebudowano profili: {error}",
    ),
    "The filament presets were not rebuilt: {error}": (
        "Os perfis de filamento não foram recriados: {error}",
        "Los perfiles de filamento no se reconstruyeron: {error}",
        "Die Filamentprofile wurden nicht neu erstellt: {error}",
        "耗材丝预设未重建：{error}",
        "Nie przebudowano profili filamentu: {error}",
    ),
    "The filament presets could not be updated: {error}": (
        "Não foi possível atualizar os perfis de filamento: {error}",
        "No se pudieron actualizar los perfiles de filamento: {error}",
        "Die Filamentprofile konnten nicht aktualisiert werden: {error}",
        "无法更新耗材丝预设：{error}",
        "Nie udało się zaktualizować profili filamentu: {error}",
    ),
    "Synced {count} filament presets from Spoolman.": (
        "{count} perfis de filamento sincronizados do Spoolman.",
        "Se sincronizaron {count} perfiles de filamento desde Spoolman.",
        "{count} Filamentprofile aus Spoolman synchronisiert.",
        "已从 Spoolman 同步 {count} 个耗材丝预设。",
        "Zsynchronizowano profile filamentu ze Spoolmana: {count}.",
    ),
    "Setting a printer's spool needs Spoolman as the spool source.": (
        "Definir a bobina de uma impressora exige o Spoolman como origem das bobinas.",
        "Para asignar el carrete de una impresora, Spoolman debe ser el origen de los carretes.",
        "Zum Festlegen der Spule eines Druckers muss Spoolman die Spulenquelle sein.",
        "设置打印机的料盘需要以 Spoolman 作为料盘来源。",
        "Ustawienie szpuli drukarki wymaga Spoolmana jako źródła szpul.",
    ),
    "Spooler can only set the spool on a single-extruder Klipper printer.": (
        "O Spooler só consegue definir a bobina em uma impressora Klipper de uma extrusora.",
        "Spooler solo puede asignar el carrete en una impresora Klipper de un extrusor.",
        "Spooler kann die Spule nur bei einem Klipper-Drucker mit einem Extruder festlegen.",
        "Spooler 只能为单挤出机的 Klipper 打印机设置料盘。",
        "Spooler może ustawić szpulę tylko w drukarce Klipper z jednym ekstruderem.",
    ),
    "{printer}: no active spool, Moonraker stopped booking usage.": (
        "{printer}: nenhuma bobina ativa, o Moonraker parou de registrar o consumo.",
        "{printer}: sin carrete activo, Moonraker dejó de registrar el consumo.",
        "{printer}: keine aktive Spule, Moonraker bucht keinen Verbrauch mehr.",
        "{printer}：没有活动料盘，Moonraker 已停止记录用量。",
        "{printer}: brak aktywnej szpuli, Moonraker przestał księgować zużycie.",
    ),
    "{printer} manages its own spools; Spooler only reads them.": (
        "{printer} gerencia as próprias bobinas; o Spooler só as lê.",
        "{printer} gestiona sus propios carretes; Spooler solo los lee.",
        "{printer} verwaltet seine Spulen selbst; Spooler liest sie nur.",
        "{printer} 自行管理料盘；Spooler 只读取它们。",
        "{printer} sam zarządza swoimi szpulami; Spooler tylko je odczytuje.",
    ),
    "{printer} is paused in a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está com uma impressão pausada: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} tiene una impresión en pausa: Moonraker registraría el resto de esta impresión en el nuevo carrete. Confirma para cambiarlo de todos modos.",
        "{printer} hat einen pausierten Druck: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 有一个已暂停的打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
        "{printer} ma wstrzymany wydruk: Moonraker zaksięgowałby resztę tego wydruku na nową szpulę. Potwierdź, aby mimo to ją zmienić.",
    ),
    "{printer} is running a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está imprimindo: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} está imprimiendo: Moonraker registraría el resto de esta impresión en el nuevo carrete. Confirma para cambiarlo de todos modos.",
        "{printer} druckt gerade: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 正在打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
        "{printer} drukuje: Moonraker zaksięgowałby resztę tego wydruku na nową szpulę. Potwierdź, aby mimo to ją zmienić.",
    ),
    "Could not set the spool on {printer}: {error}": (
        "Não foi possível definir a bobina em {printer}: {error}",
        "No se pudo asignar el carrete en {printer}: {error}",
        "Die Spule konnte auf {printer} nicht festgelegt werden: {error}",
        "无法为 {printer} 设置料盘：{error}",
        "Nie można ustawić szpuli w {printer}: {error}",
    ),
    "That spool isn't in Spoolman, or it is archived.": (
        "Essa bobina não está no Spoolman ou está arquivada.",
        "Ese carrete no está en Spoolman o está archivado.",
        "Diese Spule ist nicht in Spoolman oder archiviert.",
        "该料盘不在 Spoolman 中，或已归档。",
        "Tej szpuli nie ma w Spoolmanie albo jest zarchiwizowana.",
    ),
    "Spool #{id} set from a scale weight of {grams} g.": (
        "Bobina #{id} ajustada pelo peso na balança de {grams} g.",
        "Carrete #{id} ajustado con un peso en báscula de {grams} g.",
        "Spule #{id} nach einem Waagengewicht von {grams} g gesetzt.",
        "已按称重 {grams} g 设置料盘 #{id}。",
        "Ustawiono szpulę #{id} według pomiaru na wadze: {grams} g.",
    ),
    "Spool #{id} archived.": (
        "Bobina #{id} arquivada.",
        "Carrete #{id} archivado.",
        "Spule #{id} archiviert.",
        "料盘 #{id} 已归档。",
        "Zarchiwizowano szpulę #{id}.",
    ),
    "Spool #{id} unarchived.": (
        "Bobina #{id} desarquivada.",
        "Carrete #{id} desarchivado.",
        "Spule #{id} wiederhergestellt.",
        "料盘 #{id} 已取消归档。",
        "Przywrócono szpulę #{id} z archiwum.",
    ),
    "Spool #{id} marked as dried today.": (
        "Bobina #{id} marcada como secada hoje.",
        "Carrete #{id} marcado como secado hoy.",
        "Spule #{id} als heute getrocknet markiert.",
        "料盘 #{id} 已标记为今天烘干。",
        "Oznaczono szpulę #{id} jako wysuszoną dzisiaj.",
    ),
    "Spool #{id} has no dried date now.": (
        "A bobina #{id} agora não tem data de secagem.",
        "El carrete #{id} ya no tiene fecha de secado.",
        "Spule #{id} hat jetzt kein Trocknungsdatum.",
        "料盘 #{id} 现在没有烘干日期。",
        "Szpula #{id} nie ma już daty suszenia.",
    ),
    "Spool #{id} now has {grams} g left.": (
        "A bobina #{id} agora tem {grams} g restantes.",
        "Al carrete #{id} ahora le quedan {grams} g.",
        "Spule #{id} hat jetzt noch {grams} g.",
        "料盘 #{id} 现在剩余 {grams} g。",
        "Na szpuli #{id} zostało teraz {grams} g.",
    ),
    "Spool #{id} moved to {location}.": (
        "Bobina #{id} movida para {location}.",
        "Carrete #{id} movido a {location}.",
        "Spule #{id} nach {location} verschoben.",
        "料盘 #{id} 已移至 {location}。",
        "Przeniesiono szpulę #{id} do: {location}.",
    ),
    "Spooler can only link a spool to a Snapmaker U1 toolhead or an Anycubic Kobra ACE or spool holder slot.": (
        "O Spooler só vincula uma bobina a uma cabeça da Snapmaker U1 ou a um slot do ACE ou do suporte de carretel da Anycubic Kobra.",
        "Spooler solo vincula un carrete a un cabezal de la Snapmaker U1 o a una ranura del ACE o del portabobinas de Anycubic Kobra.",
        "Spooler verknüpft eine Spule nur mit einem Werkzeugkopf des Snapmaker U1 oder einem Slot des ACE oder Spulenhalters von Anycubic Kobra.",
        "Spooler 只能将料盘关联到 Snapmaker U1 的工具头，或 Anycubic Kobra 的 ACE 或料盘架槽位。",
        "Spooler łączy szpulę tylko z głowicą Snapmaker U1 albo ze slotem ACE lub uchwytu na szpule Anycubic Kobra.",
    ),
    "Spool #{id} isn't linked to {slot}.": (
        "A bobina #{id} não está vinculada a {slot}.",
        "El carrete #{id} no está vinculado a {slot}.",
        "Spule #{id} ist nicht mit {slot} verknüpft.",
        "料盘 #{id} 未关联到 {slot}。",
        "Szpula #{id} nie jest połączona z: {slot}.",
    ),
    "Spool #{id} is no longer linked to {slot}.": (
        "A bobina #{id} não está mais vinculada a {slot}.",
        "El carrete #{id} ya no está vinculado a {slot}.",
        "Spule #{id} ist nicht mehr mit {slot} verknüpft.",
        "料盘 #{id} 已不再关联到 {slot}。",
        "Szpula #{id} nie jest już połączona z: {slot}.",
    ),
    "Spool #{id} linked to {slot}.": (
        "Bobina #{id} vinculada a {slot}.",
        "Carrete #{id} vinculado a {slot}.",
        "Spule #{id} mit {slot} verknüpft.",
        "料盘 #{id} 已关联到 {slot}。",
        "Połączono szpulę #{id} z: {slot}.",
    ),
    "Spool #{id} has no location now.": (
        "A bobina #{id} agora não tem local.",
        "El carrete #{id} ya no tiene ubicación.",
        "Spule #{id} hat jetzt keinen Lagerort.",
        "料盘 #{id} 现在没有位置。",
        "Szpula #{id} nie ma już lokalizacji.",
    ),
    "Saved the note on spool #{id}.": (
        "Nota da bobina #{id} salva.",
        "Nota del carrete #{id} guardada.",
        "Notiz zu Spule #{id} gespeichert.",
        "已保存料盘 #{id} 的备注。",
        "Zapisano notatkę szpuli #{id}.",
    ),
    "Spool #{id} has no note now.": (
        "A bobina #{id} agora não tem nota.",
        "El carrete #{id} ya no tiene nota.",
        "Spule #{id} hat jetzt keine Notiz.",
        "料盘 #{id} 现在没有备注。",
        "Szpula #{id} nie ma już notatki.",
    ),
    "Added spool {spool} of the same filament.": (
        "Bobina {spool} do mesmo filamento adicionada.",
        "Se añadió el carrete {spool} del mismo filamento.",
        "Spule {spool} mit demselben Filament hinzugefügt.",
        "已添加相同耗材丝的料盘 {spool}。",
        "Dodano szpulę {spool} tego samego filamentu.",
    ),
    "Added {count} spools of the same filament: {spools}.": (
        "{count} bobinas do mesmo filamento adicionadas: {spools}.",
        "Se añadieron {count} carretes del mismo filamento: {spools}.",
        "{count} Spulen mit demselben Filament hinzugefügt: {spools}.",
        "已添加 {count} 个相同耗材丝的料盘：{spools}。",
        "Dodano szpule tego samego filamentu ({count}): {spools}.",
    ),
    "This Spoolman can't remove a spool's dried date; Spoolman 0.26 or newer can. Nothing was written; mark it dried again to change the date.": (
        "Este Spoolman não consegue remover a data de secagem de uma bobina; o Spoolman 0.26 ou mais recente consegue. Nada foi gravado; marque como secada de novo para mudar a data.",
        "Este Spoolman no puede quitar la fecha de secado de un carrete; Spoolman 0.26 o posterior sí puede. No se guardó nada; márcalo como secado de nuevo para cambiar la fecha.",
        "Dieses Spoolman kann das Trocknungsdatum einer Spule nicht entfernen; Spoolman 0.26 oder neuer kann es. Es wurde nichts geschrieben; markiere sie erneut als getrocknet, um das Datum zu ändern.",
        "此 Spoolman 无法移除料盘的烘干日期；Spoolman 0.26 或更新版本可以。未写入任何内容；再次标记为已烘干即可更改日期。",
        "Ten Spoolman nie potrafi usunąć daty suszenia szpuli; potrafi to Spoolman 0.26 lub nowszy. Niczego nie zapisano; oznacz szpulę ponownie jako wysuszoną, aby zmienić datę.",
    ),
    "The value for {field} isn't valid; nothing was written.": (
        "O valor de {field} não é válido; nada foi gravado.",
        "El valor de {field} no es válido; no se guardó nada.",
        "Der Wert für {field} ist ungültig; es wurde nichts geschrieben.",
        "{field} 的值无效；未写入任何内容。",
        "Wartość pola {field} jest nieprawidłowa; niczego nie zapisano.",
    ),
    "Spooler couldn't read Spoolman's version, so it can't tell how this Spoolman saves extra fields. Nothing was written; check the connection and try again.": (
        "O Spooler não conseguiu ler a versão do Spoolman, então não sabe como este Spoolman salva campos extras. Nada foi gravado; confira a conexão e tente de novo.",
        "Spooler no pudo leer la versión de Spoolman, así que no sabe cómo guarda este Spoolman los campos extra. No se guardó nada; revisa la conexión y vuelve a intentarlo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, wie dieses Spoolman Zusatzfelder speichert. Es wurde nichts geschrieben; prüfe die Verbindung und versuche es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法判断此 Spoolman 如何保存额外字段。未写入任何内容；请检查连接后重试。",
        "Spooler nie mógł odczytać wersji Spoolmana, więc nie wie, jak ten Spoolman zapisuje dodatkowe pola. Niczego nie zapisano; sprawdź połączenie i spróbuj ponownie.",
    ),
    "This Spoolman can't empty an extra field ({fields}); Spoolman 0.26 or newer can. Nothing was written.": (
        "Este Spoolman não consegue esvaziar um campo extra ({fields}); o Spoolman 0.26 ou mais recente consegue. Nada foi gravado.",
        "Este Spoolman no puede vaciar un campo extra ({fields}); Spoolman 0.26 o posterior sí puede. No se guardó nada.",
        "Dieses Spoolman kann ein Zusatzfeld nicht leeren ({fields}); Spoolman 0.26 oder neuer kann es. Es wurde nichts geschrieben.",
        "此 Spoolman 无法清空额外字段（{fields}）；Spoolman 0.26 或更新版本可以。未写入任何内容。",
        "Ten Spoolman nie potrafi wyczyścić dodatkowego pola ({fields}); potrafi to Spoolman 0.26 lub nowszy. Niczego nie zapisano.",
    ),
    "Spooler couldn't read the extra fields Spoolman holds, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras que o Spoolman guarda, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra que guarda Spoolman, y esta versión de Spoolman los reemplaza todos en cada cambio. No se guardó nada.",
        "Spooler konnte die Zusatzfelder in Spoolman nicht lesen, und diese Spoolman-Version ersetzt bei jeder Änderung alle. Es wurde nichts geschrieben.",
        "Spooler 无法读取 Spoolman 中的额外字段，而此 Spoolman 版本每次更改都会替换全部额外字段。未写入任何内容。",
        "Spooler nie mógł odczytać dodatkowych pól przechowywanych w Spoolmanie, a ta wersja Spoolmana przy zmianie zastępuje je wszystkie. Niczego nie zapisano.",
    ),
    "Saved the filament of spool #{id}, but Spoolman refused the spool: {error}": (
        "O filamento da bobina #{id} foi salvo, mas o Spoolman recusou a bobina: {error}",
        "Se guardó el filamento del carrete #{id}, pero Spoolman rechazó el carrete: {error}",
        "Das Filament von Spule #{id} wurde gespeichert, aber Spoolman hat die Spule abgelehnt: {error}",
        "已保存料盘 #{id} 的耗材丝，但 Spoolman 拒绝了料盘：{error}",
        "Zapisano filament szpuli #{id}, ale Spoolman odrzucił szpulę: {error}",
    ),
    "Saved spool #{id} and its filament.": (
        "Bobina #{id} e seu filamento salvos.",
        "Se guardaron el carrete #{id} y su filamento.",
        "Spule #{id} und ihr Filament gespeichert.",
        "已保存料盘 #{id} 及其耗材丝。",
        "Zapisano szpulę #{id} i jej filament.",
    ),
    "Saved spool #{id}.": (
        "Bobina #{id} salva.",
        "Carrete #{id} guardado.",
        "Spule #{id} gespeichert.",
        "已保存料盘 #{id}。",
        "Zapisano szpulę #{id}.",
    ),
    "Spool #{id} had no changes to save.": (
        "A bobina #{id} não tinha alterações para salvar.",
        "El carrete #{id} no tenía cambios que guardar.",
        "Spule #{id} hatte keine Änderungen zum Speichern.",
        "料盘 #{id} 没有需要保存的更改。",
        "Szpula #{id} nie miała zmian do zapisania.",
    ),
    "Kept Spoolman's newer value for {fields}: it changed there while you were editing.": (
        "O valor mais recente do Spoolman foi mantido para {fields}: ele mudou lá enquanto você editava.",
        "Se mantuvo el valor más reciente de Spoolman para {fields}: cambió allí mientras editabas.",
        "Der neuere Wert aus Spoolman wurde für {fields} behalten: Er hat sich dort während deiner Bearbeitung geändert.",
        "已保留 Spoolman 中 {fields} 的较新值：你编辑期间它在那里被更改了。",
        "Zachowano nowszą wartość ze Spoolmana dla: {fields}. Zmieniła się tam w trakcie twojej edycji.",
    ),
    "Created filament #{filament}, but Spoolman refused the spool: {error}": (
        "Filamento #{filament} criado, mas o Spoolman recusou a bobina: {error}",
        "Se creó el filamento #{filament}, pero Spoolman rechazó el carrete: {error}",
        "Filament #{filament} angelegt, aber Spoolman hat die Spule abgelehnt: {error}",
        "已创建耗材丝 #{filament}，但 Spoolman 拒绝了料盘：{error}",
        "Utworzono filament #{filament}, ale Spoolman odrzucił szpulę: {error}",
    ),
    "Added spool #{id} with the new filament #{filament}.": (
        "Bobina #{id} adicionada com o novo filamento #{filament}.",
        "Se añadió el carrete #{id} con el nuevo filamento #{filament}.",
        "Spule #{id} mit dem neuen Filament #{filament} hinzugefügt.",
        "已添加料盘 #{id}，使用新耗材丝 #{filament}。",
        "Dodano szpulę #{id} z nowym filamentem #{filament}.",
    ),
    "Added spool #{id}.": (
        "Bobina #{id} adicionada.",
        "Se añadió el carrete #{id}.",
        "Spule #{id} hinzugefügt.",
        "已添加料盘 #{id}。",
        "Dodano szpulę #{id}.",
    ),
    "Archived spool #{id} carries this RFID tag; unarchive it instead. Nothing was written.": (
        "A bobina arquivada #{id} tem esta etiqueta RFID; desarquive-a. Nada foi gravado.",
        "El carrete archivado #{id} tiene esta etiqueta RFID; desarchívelo. No se escribió nada.",
        "Die archivierte Spule #{id} trägt dieses RFID-Tag; holen Sie sie aus dem Archiv. Es wurde nichts geschrieben.",
        "已归档的料盘 #{id} 带有此 RFID 标签，请取消归档。未写入任何内容。",
        "Ten tag RFID ma zarchiwizowana szpula #{id}; przywróć ją z archiwum. Niczego nie zapisano.",
    ),
    "Spool #{id} already carries this RFID tag; nothing was written.": (
        "A bobina #{id} já tem esta etiqueta RFID; nada foi gravado.",
        "El carrete #{id} ya tiene esta etiqueta RFID; no se escribió nada.",
        "Spule #{id} trägt dieses RFID-Tag bereits; es wurde nichts geschrieben.",
        "料盘 #{id} 已带有此 RFID 标签；未写入任何内容。",
        "Szpula #{id} ma już ten tag RFID; niczego nie zapisano.",
    ),
    "Spoolman's spool field \"tag\" isn't a text field, so the RFID tag can't be stored; nothing was written.": (
        "O campo \"tag\" das bobinas no Spoolman não é um campo de texto, então a etiqueta RFID não pode ser guardada; nada foi gravado.",
        "El campo \"tag\" de los carretes en Spoolman no es un campo de texto, así que la etiqueta RFID no se puede guardar; no se escribió nada.",
        "Das Spulenfeld \"tag\" in Spoolman ist kein Textfeld, daher kann das RFID-Tag nicht gespeichert werden; es wurde nichts geschrieben.",
        "Spoolman 的料盘字段“tag”不是文本字段，无法保存 RFID 标签；未写入任何内容。",
        "Pole szpuli „tag” w Spoolmanie nie jest polem tekstowym, więc nie można zapisać tagu RFID; niczego nie zapisano.",
    ),
    "Added spool {spools}, then Spoolman refused the next one: {error}": (
        "Bobina {spools} adicionada, depois o Spoolman recusou a próxima: {error}",
        "Se añadió el carrete {spools} y luego Spoolman rechazó el siguiente: {error}",
        "Spule {spools} hinzugefügt, dann hat Spoolman die nächste abgelehnt: {error}",
        "已添加料盘 {spools}，随后 Spoolman 拒绝了下一个：{error}",
        "Dodano szpulę {spools}, a potem Spoolman odrzucił następną: {error}",
    ),
    "Opened spool #{id} in Spoolman.": (
        "Bobina #{id} aberta no Spoolman.",
        "Carrete #{id} abierto en Spoolman.",
        "Spule #{id} in Spoolman geöffnet.",
        "已在 Spoolman 中打开料盘 #{id}。",
        "Otwarto szpulę #{id} w Spoolmanie.",
    ),
    "Unknown spool action.": (
        "Ação de bobina desconhecida.",
        "Acción de carrete desconocida.",
        "Unbekannte Spulenaktion.",
        "未知的料盘操作。",
        "Nieznana akcja na szpuli.",
    ),
    "Spool actions need Spoolman as the source.": (
        "As ações de bobina exigem o Spoolman como origem.",
        "Las acciones de carrete necesitan Spoolman como origen.",
        "Spulenaktionen erfordern Spoolman als Quelle.",
        "料盘操作需要以 Spoolman 作为来源。",
        "Akcje na szpulach wymagają Spoolmana jako źródła.",
    ),
    "That preset can't be used for this filament on this printer.": (
        "Esse perfil não serve para este filamento nesta impressora.",
        "Ese perfil no sirve para este filamento en esta impresora.",
        "Dieses Profil passt nicht zu diesem Filament auf diesem Drucker.",
        "该预设不适用于此打印机上的这种耗材丝。",
        "Ten profil nie pasuje do tego filamentu na tej drukarce.",
    ),
    "The Open Filament Database preset can't be used: {why}": (
        "O perfil da Open Filament Database não pode ser usado: {why}",
        "El perfil de la Open Filament Database no se puede usar: {why}",
        "Das Profil aus der Open Filament Database kann nicht verwendet werden: {why}",
        "无法使用 Open Filament Database 的预设：{why}",
        "Profilu z Open Filament Database nie można użyć: {why}",
    ),
    "Its presets use the Open Filament Database preset on {printers}.": (
        "Os perfis dela usam o perfil da Open Filament Database em {printers}.",
        "Sus perfiles usan el perfil de la Open Filament Database en {printers}.",
        "Ihre Profile nutzen das Profil aus der Open Filament Database für {printers}.",
        "其预设在 {printers} 上使用 Open Filament Database 的预设。",
        "Jej profile używają profilu z Open Filament Database na {printers}.",
    ),
    "The Open Filament Database preset fits none of your printers, so Spooler picks the preset itself.": (
        "O perfil da Open Filament Database não serve para nenhuma das suas impressoras; o Spooler escolhe o perfil sozinho.",
        "El perfil de la Open Filament Database no sirve para ninguna de sus impresoras; Spooler elige el perfil por sí mismo.",
        "Das Profil aus der Open Filament Database passt zu keinem Ihrer Drucker; Spooler wählt das Profil selbst.",
        "Open Filament Database 的预设不适用于您的任何打印机，Spooler 会自行选择预设。",
        "Profil z Open Filament Database nie pasuje do żadnej z drukarek, więc Spooler sam wybierze profil.",
    ),
    "No spool chosen.": (
        "Nenhuma bobina escolhida.",
        "No se eligió ningún carrete.",
        "Keine Spule ausgewählt.",
        "未选择料盘。",
        "Nie wybrano szpuli.",
    ),
    "The spool source changed since this list was read; nothing was written. Refresh and try again.": (
        "A origem das bobinas mudou desde que esta lista foi lida; nada foi gravado. Atualize e tente de novo.",
        "El origen de los carretes cambió desde que se leyó esta lista; no se escribió nada. Actualiza e inténtalo de nuevo.",
        "Die Spulenquelle hat sich seit dem Lesen dieser Liste geändert; es wurde nichts geschrieben. Aktualisieren Sie und versuchen Sie es erneut.",
        "读取此列表后料盘来源已更改；未写入任何内容。请刷新后重试。",
        "Źródło szpul zmieniło się od wczytania tej listy; niczego nie zapisano. Odśwież i spróbuj ponownie.",
    ),
    "Spoolman has the change, but Spooler could not update its history file.": (
        "O Spoolman tem a alteração, mas o Spooler não conseguiu atualizar seu arquivo de histórico.",
        "Spoolman tiene el cambio, pero Spooler no pudo actualizar su archivo de historial.",
        "Spoolman hat die Änderung, aber Spooler konnte seine Verlaufsdatei nicht aktualisieren.",
        "Spoolman 已有该更改，但 Spooler 无法更新其历史文件。",
        "Spoolman ma już zmianę, ale Spooler nie mógł zaktualizować swojego pliku historii.",
    ),
    "This print was recorded for another spool source, or before Spooler noted which Spoolman it belongs to, so Spooler won't book it here. If it is still owed, book it in Spoolman by hand.": (
        "Esta impressão foi registrada para outra origem de bobinas, ou antes de o Spooler anotar a qual Spoolman ela pertence, então o Spooler não vai lançá-la aqui. Se ainda estiver pendente, lance-a à mão no Spoolman.",
        "Esta impresión se registró para otro origen de carretes, o antes de que Spooler anotara a qué Spoolman pertenece, así que Spooler no la registrará aquí. Si sigue pendiente, regístrala a mano en Spoolman.",
        "Dieser Druck wurde für eine andere Spulenquelle erfasst oder bevor Spooler vermerkt hat, zu welchem Spoolman er gehört, daher bucht Spooler ihn hier nicht. Falls er noch offen ist, buchen Sie ihn von Hand in Spoolman.",
        "此打印记录属于另一个料盘来源，或记录于 Spooler 标明其所属 Spoolman 之前，因此 Spooler 不会在此记账。如果仍需记录，请在 Spoolman 中手动记录。",
        "Ten wydruk zapisano dla innego źródła szpul albo zanim Spooler zanotował, do którego Spoolmana należy, więc Spooler go tu nie zaksięguje. Jeśli nadal trzeba go rozliczyć, zaksięguj go w Spoolmanie ręcznie.",
    ),
    "Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use booked meanwhile. Spooler couldn't confirm this Spoolman's version, so nothing changed; adjust the spools in Spoolman by hand.": (
        "Desfazer exige o Spoolman 0.18 ou mais recente, que devolve os gramas em uma etapa sem perder o consumo registrado nesse meio-tempo. O Spooler não conseguiu confirmar a versão deste Spoolman, então nada mudou; ajuste as bobinas à mão no Spoolman.",
        "Deshacer necesita Spoolman 0.18 o posterior, que devuelve los gramos en un solo paso sin perder el consumo registrado mientras tanto. Spooler no pudo confirmar la versión de este Spoolman, así que no cambió nada; ajusta los carretes a mano en Spoolman.",
        "Rückgängig machen erfordert Spoolman 0.18 oder neuer, das Gramm in einem Schritt zurückbucht, ohne zwischenzeitlich gebuchten Verbrauch zu verlieren. Spooler konnte die Version dieses Spoolman nicht bestätigen, daher wurde nichts geändert; passen Sie die Spulen von Hand in Spoolman an.",
        "撤销需要 Spoolman 0.18 或更新版本，它能一步加回克数，且不会丢失期间记录的用量。Spooler 无法确认此 Spoolman 的版本，因此未做任何更改；请在 Spoolman 中手动调整料盘。",
        "Cofanie wymaga Spoolmana 0.18 lub nowszego, który oddaje gramy w jednym kroku, nie gubiąc zużycia zaksięgowanego w międzyczasie. Spooler nie mógł potwierdzić wersji tego Spoolmana, więc nic nie zmieniono; popraw szpule w Spoolmanie ręcznie.",
    ),
    "Spooler could not save its booking state ({file}), so it stopped. Rows it was sending are marked for you to check in Spoolman.": (
        "O Spooler não conseguiu salvar seu estado de lançamentos ({file}), então parou. As linhas que ele estava enviando estão marcadas para você conferir no Spoolman.",
        "Spooler no pudo guardar su estado de registros ({file}), así que se detuvo. Las filas que estaba enviando quedan marcadas para que las revises en Spoolman.",
        "Spooler konnte seinen Buchungsstand ({file}) nicht speichern und hat daher angehalten. Zeilen, die gerade gesendet wurden, sind markiert, damit Sie sie in Spoolman prüfen.",
        "Spooler 无法保存其记账状态（{file}），因此已停止。正在发送的行已标记，请在 Spoolman 中核对。",
        "Spooler nie mógł zapisać stanu księgowania ({file}), więc przerwał. Wiersze, które wysyłał, oznaczono do sprawdzenia w Spoolmanie.",
    ),
    "Spooler can't tell whether Spoolman applied this. Check the spool in Spoolman, then say which.": (
        "O Spooler não sabe se o Spoolman aplicou isto. Confira a bobina no Spoolman e diga o que aconteceu.",
        "Spooler no sabe si Spoolman aplicó esto. Revisa el carrete en Spoolman y di qué ocurrió.",
        "Spooler kann nicht erkennen, ob Spoolman dies übernommen hat. Prüfen Sie die Spule in Spoolman und geben Sie an, was zutrifft.",
        "Spooler 无法确定 Spoolman 是否已应用此操作。请在 Spoolman 中检查料盘，然后说明结果。",
        "Spooler nie wie, czy Spoolman to zastosował. Sprawdź szpulę w Spoolmanie, a potem wskaż, jak jest.",
    ),
    "Other": (
        "Outro",
        "Otro",
        "Sonstiges",
        "其他",
        "Inne",
    ),
    "Could not reach GitHub ({reason})": (
        "Não foi possível acessar o GitHub ({reason})",
        "No se pudo conectar con GitHub ({reason})",
        "GitHub ist nicht erreichbar ({reason})",
        "无法连接 GitHub（{reason}）",
        "Nie można połączyć z GitHubem ({reason})",
    ),
    "GitHub sent an answer Spooler doesn't understand": (
        "O GitHub enviou uma resposta que o Spooler não entende",
        "GitHub envió una respuesta que Spooler no entiende",
        "GitHub hat eine Antwort gesendet, die Spooler nicht versteht",
        "GitHub 返回了 Spooler 无法识别的回复",
        "GitHub wysłał odpowiedź, której Spooler nie rozumie",
    ),
    "No published release found yet": (
        "Nenhuma versão publicada ainda",
        "Aún no hay ninguna versión publicada",
        "Noch keine veröffentlichte Version gefunden",
        "尚未找到已发布的版本",
        "Nie znaleziono jeszcze opublikowanego wydania",
    ),
    "GitHub returned HTTP {code}": (
        "O GitHub retornou HTTP {code}",
        "GitHub devolvió HTTP {code}",
        "GitHub meldete HTTP {code}",
        "GitHub 返回 HTTP {code}",
        "GitHub zwrócił HTTP {code}",
    ),
    "{slot} {need} but {supply}{tracked}": (
        "{slot} {need}, mas {supply}{tracked}",
        "{slot} {need}, pero {supply}{tracked}",
        "{slot} {need}, aber {supply}{tracked}",
        "{slot}{need}，但{supply}{tracked}",
        "{slot} {need}, ale {supply}{tracked}",
    ),
    " Swap in spool #{id} ({location}, {grams} g).": (
        " Troque pela bobina #{id} ({location}, {grams} g).",
        " Cambia al carrete #{id} ({location}, {grams} g).",
        " Wechseln Sie zu Spule #{id} ({location}, {grams} g).",
        "可换用料盘 #{id}（{location}，{grams} g）。",
        " Załóż szpulę #{id} ({location}, {grams} g).",
    ),
    " Swap in spool #{id} ({grams} g).": (
        " Troque pela bobina #{id} ({grams} g).",
        " Cambia al carrete #{id} ({grams} g).",
        " Wechseln Sie zu Spule #{id} ({grams} g).",
        "可换用料盘 #{id}（{grams} g）。",
        " Załóż szpulę #{id} ({grams} g).",
    ),
    "of {matches} matching spools the fullest has {have} and the smallest has {worst}, so make sure the right one is loaded": (
        "das {matches} bobinas compatíveis, a mais cheia tem {have} e a mais vazia tem {worst}, então confira se a certa está carregada",
        "de {matches} carretes compatibles, el más lleno tiene {have} y el más vacío {worst}, así que asegúrate de que esté cargado el correcto",
        "von {matches} passenden Spulen hat die vollste {have} und die leerste {worst}, also achten Sie darauf, dass die richtige geladen ist",
        "在 {matches} 个匹配料盘中，最满的有 {have}，最少的只有 {worst}，请确认装入的是正确的料盘",
        "spośród {matches} pasujących szpul najpełniejsza ma {have}, a najmniej pełna {worst}, więc upewnij się, że załadowano właściwą",
    ),
    "the {count} fullest of {matches} matching spools hold {have} and the {count} smallest hold {worst}, so make sure the right ones are loaded": (
        "das {matches} bobinas compatíveis, as {count} mais cheias têm {have} e as {count} mais vazias têm {worst}, então confira se as certas estão carregadas",
        "de {matches} carretes compatibles, los {count} más llenos tienen {have} y los {count} más vacíos {worst}, así que asegúrate de que estén cargados los correctos",
        "von {matches} passenden Spulen haben die {count} vollsten {have} und die {count} leersten {worst}, also achten Sie darauf, dass die richtigen geladen sind",
        "在 {matches} 个匹配料盘中，最满的 {count} 个共有 {have}，最少的 {count} 个只有 {worst}，请确认装入的是正确的料盘",
        "spośród {matches} pasujących szpul najpełniejsze ({count}) mają łącznie {have}, a najmniej pełne ({count}) {worst}, więc upewnij się, że załadowano właściwe",
    ),
    "{slot} {need}; {body}": (
        "{slot} {need}; {body}",
        "{slot} {need}; {body}",
        "{slot} {need}; {body}",
        "{slot}{need}；{body}",
        "{slot} {need}; {body}",
    ),
    "{slot} {need} ({padded} with the {margin}% margin) and {supply}{tracked}": (
        "{slot} {need} ({padded} com a margem de {margin}%) e {supply}{tracked}",
        "{slot} {need} ({padded} con el margen del {margin} %) y {supply}{tracked}",
        "{slot} {need} ({padded} mit {margin} % Reserve) und {supply}{tracked}",
        "{slot}{need}（加上 {margin}% 余量为 {padded}），而{supply}{tracked}",
        "{slot} {need} ({padded} z zapasem {margin}%), a {supply}{tracked}",
    ),
    "{slot} {need}, {supply}": (
        "{slot} {need}, {supply}",
        "{slot} {need}, {supply}",
        "{slot} {need}, {supply}",
        "{slot}{need}，{supply}",
        "{slot} {need}, {supply}",
    ),
    "not enough filament loaded in the AMS.": (
        "filamento insuficiente carregado no AMS.",
        "no hay suficiente filamento cargado en el AMS.",
        "nicht genug Filament im AMS geladen.",
        "AMS 中装入的耗材丝不足。",
        "za mało filamentu załadowanego w AMS.",
    ),
    "not enough filament loaded.": (
        "filamento insuficiente carregado.",
        "no hay suficiente filamento cargado.",
        "nicht genug Filament geladen.",
        "装入的耗材丝不足。",
        "za mało załadowanego filamentu.",
    ),
    "not enough filament may be loaded in the AMS.": (
        "talvez não haja filamento suficiente carregado no AMS.",
        "puede que no haya suficiente filamento cargado en el AMS.",
        "möglicherweise ist nicht genug Filament im AMS geladen.",
        "AMS 中装入的耗材丝可能不足。",
        "w AMS może być za mało filamentu.",
    ),
    "not enough filament may be loaded.": (
        "talvez não haja filamento suficiente carregado.",
        "puede que no haya suficiente filamento cargado.",
        "möglicherweise ist nicht genug Filament geladen.",
        "装入的耗材丝可能不足。",
        "załadowanego filamentu może być za mało.",
    ),
    "also check: ": (
        "confira também: ",
        "revisa también: ",
        "prüfen Sie auch: ",
        "另请检查：",
        "sprawdź też: ",
    ),
    "also barely enough: ": (
        "também no limite: ",
        "también muy justo: ",
        "ebenfalls knapp: ",
        "同样勉强够用：",
        "też ledwo wystarczy: ",
    ),
    "barely enough filament.": (
        "filamento no limite.",
        "filamento muy justo.",
        "Filament knapp.",
        "耗材丝勉强够用。",
        "filamentu ledwo wystarczy.",
    ),
    "quantity OK.": (
        "quantidade OK.",
        "cantidad correcta.",
        "Menge OK.",
        "用量充足。",
        "ilość OK.",
    ),
    "quantity OK for slots {slots}.": (
        "quantidade OK para os slots {slots}.",
        "cantidad correcta para las ranuras {slots}.",
        "Menge OK für Slots {slots}.",
        "槽位 {slots} 用量充足。",
        "ilość OK dla slotów {slots}.",
    ),
    "no spool found for {slots}, so they weren't checked": (
        "nenhuma bobina encontrada para {slots}, então não foram conferidos",
        "no se encontró carrete para {slots}, así que no se comprobaron",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到{slots}的料盘，因此未检查",
        "nie znaleziono szpuli (dotyczy: {slots}), więc nie sprawdzono ilości",
    ),
    "no spool found for {slots}, so it wasn't checked": (
        "nenhuma bobina encontrada para {slots}, então não foi conferido",
        "no se encontró carrete para {slots}, así que no se comprobó",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到{slots}的料盘，因此未检查",
        "nie znaleziono szpuli (dotyczy: {slots}), więc nie sprawdzono ilości",
    ),
    "Not checked": (
        "Não conferido",
        "Sin comprobar",
        "Nicht geprüft",
        "未检查",
        "Nie sprawdzono",
    ),
    "no spool found for these slots": (
        "nenhuma bobina encontrada para estes slots",
        "no se encontró carrete para estas ranuras",
        "keine Spule für diese Slots gefunden",
        "未找到这些槽位的料盘",
        "nie znaleziono szpuli dla tych slotów",
    ),
    "no spool found for this slot": (
        "nenhuma bobina encontrada para este slot",
        "no se encontró carrete para esta ranura",
        "keine Spule für diesen Slot gefunden",
        "未找到此槽位的料盘",
        "nie znaleziono szpuli dla tego slotu",
    ),
    "Quantity OK": (
        "Quantidade OK",
        "Cantidad correcta",
        "Menge OK",
        "用量充足",
        "Ilość OK",
    ),
    "Barely enough": (
        "No limite",
        "Muy justo",
        "Knapp",
        "勉强够用",
        "Ledwo wystarczy",
    ),
    "Not enough": (
        "Insuficiente",
        "Insuficiente",
        "Nicht genug",
        "不足",
        "Za mało",
    ),
    "Check the spools": (
        "Confira as bobinas",
        "Revisa los carretes",
        "Spulen prüfen",
        "检查料盘",
        "Sprawdź szpule",
    ),
    "Check the spool": (
        "Confira a bobina",
        "Revisa el carrete",
        "Spule prüfen",
        "检查料盘",
        "Sprawdź szpulę",
    ),
    "{need} needed · matching spools hold {low} to {high}": (
        "{need} necessários · as bobinas compatíveis têm de {low} a {high}",
        "{need} necesarios · los carretes compatibles tienen de {low} a {high}",
        "{need} benötigt · passende Spulen haben {low} bis {high}",
        "需要 {need} · 匹配料盘有 {low} 至 {high}",
        "Potrzeba {need} · pasujące szpule mają od {low} do {high}",
    ),
    "{need} needed · {have} across {count} spools": (
        "{need} necessários · {have} em {count} bobinas",
        "{need} necesarios · {have} en {count} carretes",
        "{need} benötigt · {have} auf {count} Spulen",
        "需要 {need} · {count} 个料盘共 {have}",
        "Potrzeba {need} · łącznie {have} (szpule: {count})",
    ),
    "{need} needed · leaves {left}": (
        "{need} necessários · sobram {left}",
        "{need} necesarios · quedan {left}",
        "{need} benötigt · {left} bleiben übrig",
        "需要 {need} · 剩余 {left}",
        "Potrzeba {need} · zostanie {left}",
    ),
    "{need} needed · every matching spool has at least {low}": (
        "{need} necessários · toda bobina compatível tem pelo menos {low}",
        "{need} necesarios · cada carrete compatible tiene al menos {low}",
        "{need} benötigt · jede passende Spule hat mindestens {low}",
        "需要 {need} · 每个匹配料盘至少有 {low}",
        "Potrzeba {need} · każda pasująca szpula ma co najmniej {low}",
    ),
    "{need} needed · {have} left": (
        "{need} necessários · restam {have}",
        "{need} necesarios · quedan {have}",
        "{need} benötigt · {have} übrig",
        "需要 {need} · 剩余 {have}",
        "Potrzeba {need} · zostało {have}",
    ),
    "{count} slots, pooled": (
        "{count} slots, somados",
        "{count} ranuras, sumadas",
        "{count} Slots, zusammengefasst",
        "{count} 个槽位，合并计算",
        "sloty razem: {count}",
    ),
    "Spooler: no Spoolman address is set up yet, so the filament quantity wasn't checked.": (
        "Spooler: nenhum endereço do Spoolman configurado ainda, então a quantidade de filamento não foi conferida.",
        "Spooler: aún no hay una dirección de Spoolman configurada, así que no se comprobó la cantidad de filamento.",
        "Spooler: Es ist noch keine Spoolman-Adresse eingerichtet, daher wurde die Filamentmenge nicht geprüft.",
        "Spooler：尚未设置 Spoolman 地址，因此未检查耗材丝用量。",
        "Spooler: nie ustawiono jeszcze adresu Spoolmana, więc nie sprawdzono ilości filamentu.",
    ),
    "Spooler: couldn't reach {source}, so the filament quantity wasn't checked.": (
        "Spooler: não foi possível acessar {source}, então a quantidade de filamento não foi conferida.",
        "Spooler: no se pudo conectar con {source}, así que no se comprobó la cantidad de filamento.",
        "Spooler: {source} ist nicht erreichbar, daher wurde die Filamentmenge nicht geprüft.",
        "Spooler：无法连接 {source}，因此未检查耗材丝用量。",
        "Spooler: nie można połączyć z {source}, więc nie sprawdzono ilości filamentu.",
    ),
    "Could not write settings to {file}. Check that this folder is writable.": (
        "Não foi possível gravar os ajustes em {file}. Verifique se a pasta permite gravação.",
        "No se pudieron guardar los ajustes en {file}. Comprueba que se pueda escribir en esa carpeta.",
        "Die Einstellungen konnten nicht in {file} geschrieben werden. Prüfen Sie, ob dieser Ordner beschreibbar ist.",
        "无法将设置写入 {file}。请检查该文件夹是否可写。",
        "Nie można zapisać ustawień w {file}. Sprawdź, czy do tego folderu można zapisywać.",
    ),
    "{plugin} - Settings & About": (
        "{plugin} - Ajustes e Sobre",
        "{plugin} - Ajustes e información",
        "{plugin} - Einstellungen & Info",
        "{plugin} - 设置与关于",
        "{plugin} – ustawienia i informacje",
    ),
    "Opened {plugin}": (
        "{plugin} aberto",
        "{plugin} abierto",
        "{plugin} geöffnet",
        "已打开 {plugin}",
        "Otwarto {plugin}",
    ),
    "Open the {plugin} tab once, then run this again.": (
        "Abra a aba {plugin} uma vez e rode isto de novo.",
        "Abre la pestaña {plugin} una vez y vuelve a ejecutar esto.",
        "Öffnen Sie einmal den Tab {plugin} und führen Sie dies dann erneut aus.",
        "请先打开一次 {plugin} 标签页，然后再次运行。",
        "Otwórz raz kartę {plugin}, a potem uruchom to ponownie.",
    ),
    "The selected printer preset has no host address.": (
        "O perfil de impressora selecionado não tem endereço do host.",
        "El perfil de impresora seleccionado no tiene dirección de host.",
        "Das ausgewählte Druckerprofil hat keine Host-Adresse.",
        "所选打印机预设没有主机地址。",
        "Wybrany profil drukarki nie ma adresu hosta.",
    ),
    "OrcaSlicer refused a filament slot change from Spooler's background thread, so keeping the slots synced automatically is off. Use Plugins > Run > Spooler: Keep Slots Synced instead.": (
        "O OrcaSlicer recusou uma alteração de slot de filamento feita em segundo plano pelo Spooler, então a sincronização automática dos slots foi desligada. Use Plugins > Executar > Spooler: Keep Slots Synced.",
        "OrcaSlicer rechazó un cambio de ranura de filamento hecho en segundo plano por Spooler, así que la sincronización automática de ranuras quedó desactivada. Usa Plugins > Ejecutar > Spooler: Keep Slots Synced.",
        "OrcaSlicer hat eine Filament-Slot-Änderung aus dem Hintergrund-Thread von Spooler abgelehnt, daher ist das automatische Synchronisieren der Slots aus. Verwenden Sie stattdessen Plugins > Ausführen > Spooler: Keep Slots Synced.",
        "OrcaSlicer 拒绝了 Spooler 后台线程发起的耗材丝槽位更改，因此已关闭槽位自动同步。请改用 插件 > 运行 > Spooler: Keep Slots Synced。",
        "OrcaSlicer odrzucił zmianę slotu filamentu z wątku w tle Spoolera, więc automatyczna synchronizacja slotów jest wyłączona. Zamiast tego użyj Wtyczki > Uruchom > Spooler: Keep Slots Synced.",
    ),
    "Stopped keeping the filament slots synced.": (
        "Os slots de filamento não estão mais sendo sincronizados.",
        "Se dejó de sincronizar las ranuras de filamento.",
        "Die Filament-Slots werden nicht mehr synchronisiert.",
        "已停止同步耗材丝槽位。",
        "Zatrzymano synchronizację slotów filamentu.",
    ),
    "Stopped keeping the filament slots synced automatically until OrcaSlicer restarts. Run this again to keep them synced, or turn the setting off and on to restart it.": (
        "A sincronização automática dos slots de filamento parou até o OrcaSlicer reiniciar. Rode isto de novo para mantê-los sincronizados, ou desligue e ligue o ajuste para reiniciá-la.",
        "Se dejó de sincronizar automáticamente las ranuras de filamento hasta que OrcaSlicer se reinicie. Vuelve a ejecutar esto para mantenerlas sincronizadas, o desactiva y activa el ajuste para reiniciarla.",
        "Die automatische Synchronisierung der Filament-Slots ist bis zum Neustart von OrcaSlicer beendet. Führen Sie dies erneut aus, um sie synchron zu halten, oder schalten Sie die Einstellung aus und wieder ein.",
        "已停止自动同步耗材丝槽位，直到 OrcaSlicer 重启。再次运行可继续同步，或将该设置关闭再打开以重新启动。",
        "Zatrzymano automatyczną synchronizację slotów filamentu do ponownego uruchomienia OrcaSlicer. Uruchom to ponownie, aby dalej synchronizować, albo wyłącz i włącz ustawienie, aby ją wznowić.",
    ),
    "Keep Slots Synced is already running.": (
        "Keep Slots Synced já está em execução.",
        "Keep Slots Synced ya se está ejecutando.",
        "Keep Slots Synced läuft bereits.",
        "Keep Slots Synced 已在运行。",
        "Keep Slots Synced już działa.",
    ),
    "Spoolman sent a spool list Spooler doesn't understand": (
        "O Spoolman enviou uma lista de bobinas que o Spooler não entende",
        "Spoolman envió una lista de carretes que Spooler no entiende",
        "Spoolman hat eine Spulenliste gesendet, die Spooler nicht versteht",
        "Spoolman 返回了 Spooler 无法识别的料盘列表",
        "Spoolman wysłał listę szpul, której Spooler nie rozumie",
    ),
    "Syncing presets needs Spoolman as the source.": (
        "Sincronizar perfis exige o Spoolman como origem.",
        "Sincronizar perfiles necesita Spoolman como origen.",
        "Das Synchronisieren von Presets erfordert Spoolman als Quelle.",
        "同步预设需要以 Spoolman 作为来源。",
        "Synchronizacja profili wymaga Spoolmana jako źródła.",
    ),
    "Could not read OrcaSlicer's presets.": (
        "Não foi possível ler os perfis do OrcaSlicer.",
        "No se pudieron leer los perfiles de OrcaSlicer.",
        "Die OrcaSlicer-Profile konnten nicht gelesen werden.",
        "无法读取 OrcaSlicer 的预设。",
        "Nie można odczytać profili OrcaSlicer.",
    ),
    "Already sending to Spoolman; try again in a moment.": (
        "Já enviando ao Spoolman; tente de novo daqui a pouco.",
        "Ya se está enviando a Spoolman; inténtalo de nuevo en un momento.",
        "Es wird bereits an Spoolman gesendet; versuchen Sie es gleich erneut.",
        "正在发送到 Spoolman；请稍后重试。",
        "Trwa już wysyłanie do Spoolmana; spróbuj ponownie za chwilę.",
    ),
    "Sending needs Spoolman as the source.": (
        "O envio exige o Spoolman como origem.",
        "Enviar necesita Spoolman como origen.",
        "Senden erfordert Spoolman als Quelle.",
        "发送需要以 Spoolman 作为来源。",
        "Wysyłanie wymaga Spoolmana jako źródła.",
    ),
    "Enter a weight between 0 and {max} g.": (
        "Digite um peso entre 0 e {max} g.",
        "Introduce un peso entre 0 y {max} g.",
        "Geben Sie ein Gewicht zwischen 0 und {max} g ein.",
        "请输入 0 到 {max} g 之间的重量。",
        "Wpisz wagę od 0 do {max} g.",
    ),
    "Used {grams} g of spool #{id}.": (
        "{grams} g da bobina #{id} usados.",
        "Se usaron {grams} g del carrete #{id}.",
        "{grams} g von Spule #{id} verbraucht.",
        "已使用料盘 #{id} 的 {grams} g。",
        "Zużyto {grams} g ze szpuli #{id}.",
    ),
    "A location is text of at most {max} characters.": (
        "O local é um texto de no máximo {max} caracteres.",
        "La ubicación es un texto de {max} caracteres como máximo.",
        "Ein Lagerort ist Text mit höchstens {max} Zeichen.",
        "位置为最多 {max} 个字符的文本。",
        "Lokalizacja to tekst o długości do {max} znaków.",
    ),
    "Enter the grams left, from 0 to {max} g.": (
        "Digite os gramas restantes, de 0 a {max} g.",
        "Introduce los gramos restantes, de 0 a {max} g.",
        "Geben Sie die verbleibenden Gramm ein, von 0 bis {max} g.",
        "请输入剩余克数，0 到 {max} g。",
        "Wpisz, ile gramów zostało: od 0 do {max} g.",
    ),
    "A note is text of at most {max} characters.": (
        "A nota é um texto de no máximo {max} caracteres.",
        "La nota es un texto de {max} caracteres como máximo.",
        "Eine Notiz ist Text mit höchstens {max} Zeichen.",
        "备注为最多 {max} 个字符的文本。",
        "Notatka to tekst o długości do {max} znaków.",
    ),
    "That spool has no filament to copy.": (
        "Essa bobina não tem filamento para copiar.",
        "Ese carrete no tiene filamento que copiar.",
        "Diese Spule hat kein Filament zum Kopieren.",
        "该料盘没有可复制的耗材丝。",
        "Ta szpula nie ma filamentu do skopiowania.",
    ),
    "Add 1 to {max} spools at a time.": (
        "Adicione de 1 a {max} bobinas por vez.",
        "Añade de 1 a {max} carretes a la vez.",
        "Fügen Sie 1 bis {max} Spulen auf einmal hinzu.",
        "每次可添加 1 到 {max} 个料盘。",
        "Dodawaj od 1 do {max} szpul naraz.",
    ),
    "Could not write the export: {error}": (
        "Não foi possível gravar a exportação: {error}",
        "No se pudo escribir la exportación: {error}",
        "Der Export konnte nicht geschrieben werden: {error}",
        "无法写入导出文件：{error}",
        "Nie można zapisać eksportu: {error}",
    ),
    "Spoolman could not be read": (
        "Não foi possível ler o Spoolman",
        "No se pudo leer Spoolman",
        "Spoolman konnte nicht gelesen werden",
        "无法读取 Spoolman",
        "Nie można odczytać Spoolmana",
    ),
    "OrcaSlicer's data folder was not found": (
        "A pasta de dados do OrcaSlicer não foi encontrada",
        "No se encontró la carpeta de datos de OrcaSlicer",
        "Der Datenordner von OrcaSlicer wurde nicht gefunden",
        "未找到 OrcaSlicer 的数据文件夹",
        "Nie znaleziono folderu danych OrcaSlicer",
    ),
    "Could not read Spoolman.": (
        "Não foi possível ler o Spoolman.",
        "No se pudo leer Spoolman.",
        "Spoolman konnte nicht gelesen werden.",
        "无法读取 Spoolman。",
        "Nie można odczytać Spoolmana.",
    ),
    "{text}: {detail}": (
        "{text}: {detail}",
        "{text}: {detail}",
        "{text}: {detail}",
        "{text}：{detail}",
        "{text}: {detail}",
    ),
    "{text} ({detail})": (
        "{text} ({detail})",
        "{text} ({detail})",
        "{text} ({detail})",
        "{text}（{detail}）",
        "{text} ({detail})",
    ),
    "Spool {id}": (
        "Bobina {id}",
        "Carrete {id}",
        "Spule {id}",
        "料盘 {id}",
        "Szpula {id}",
    ),
    "spool {id}": (
        "bobina {id}",
        "carrete {id}",
        "Spule {id}",
        "料盘 {id}",
        "szpula {id}",
    ),
    "Could not read the spool list: {error}": (
        "Não foi possível ler a lista de bobinas: {error}",
        "No se pudo leer la lista de carretes: {error}",
        "Die Spulenliste konnte nicht gelesen werden: {error}",
        "无法读取料盘列表：{error}",
        "Nie można odczytać listy szpul: {error}",
    ),
    "Test the connection successfully before saving.": (
        "Teste a conexão com sucesso antes de salvar.",
        "Prueba la conexión con éxito antes de guardar.",
        "Testen Sie die Verbindung erfolgreich, bevor Sie speichern.",
        "保存前请先成功测试连接。",
        "Przed zapisaniem przetestuj połączenie.",
    ),
    "Auto Bed Levelling": (
        "Nivelamento automático da mesa",
        "Nivelación de cama automática",
        "Automatische Druckbettnivellierung",
        "自动热床调平",
        "Automatyczne poziomowanie stołu",
    ),
    "Heating Bed": (
        "Aquecendo a mesa",
        "Precalentamiento de la cama",
        "Heizbett vorheizen",
        "预加热热床",
        "Nagrzewanie stołu",
    ),
    "Sweeping XY Mech Mode": (
        "Varredura do modo mecânico XY",
        "Barrido del modo mecánico XY",
        "XY-Mechanik-Modus-Abtastung",
        "XY 机械模式扫描",
        "Sprawdzanie mechaniki XY",
    ),
    "Changing Filament": (
        "Trocando o filamento",
        "Cambiando el filamento",
        "Filament wechseln",
        "换料",
        "Zmiana filamentu",
    ),
    "Paused": (
        "Pausado",
        "En pausa",
        "Pausiert",
        "已暂停",
        "Wstrzymano",
    ),
    "Paused: Filament Runout": (
        "Pausa (fim do filamento)",
        "Pausa (filamento agotado)",
        "Pause (Filament leer)",
        "暂停（耗材丝耗尽）",
        "Pauza: koniec filamentu",
    ),
    "Heating Nozzle": (
        "Aquecendo o bico",
        "Calentando la boquilla",
        "Düse wird erhitzt",
        "加热喷嘴",
        "Nagrzewanie dyszy",
    ),
    "Calibrating Extrusion": (
        "Calibrando a extrusão",
        "Calibrando la extrusión",
        "Extrusion wird kalibriert",
        "校准挤出",
        "Kalibracja ekstruzji",
    ),
    "Scanning Bed Surface": (
        "Digitalizando a superfície da mesa",
        "Escaneando la superficie de la cama",
        "Scan der Druckbettoberfläche",
        "扫描热床",
        "Skanowanie powierzchni stołu",
    ),
    "Inspecting First Layer": (
        "Inspecionando a primeira camada",
        "Inspeccionando la primera capa",
        "Überprüfung der ersten Schicht",
        "扫描首层",
        "Sprawdzanie pierwszej warstwy",
    ),
    "Identifying Build Plate": (
        "Identificando o tipo de placa de impressão",
        "Identificando el tipo de cama de impresión",
        "Identifikation der Druckplatte",
        "识别打印板类型",
        "Rozpoznawanie płyty roboczej",
    ),
    "Calibrating Micro Lidar": (
        "Calibrando Micro Lidar",
        "Calibrando micro Lidar",
        "Kalibrierung des Mikro-Lidars",
        "校准 Micro Lidar",
        "Kalibracja Micro Lidar",
    ),
    "Homing Toolhead": (
        "Reposicionando o cabeçote",
        "Homing del cabezal",
        "Referenzfahrt des Werkzeugkopfes",
        "工具头回原点",
        "Bazowanie głowicy",
    ),
    "Cleaning Nozzle Tip": (
        "Limpando a ponta do bico",
        "Limpiando la boquilla",
        "Reinigen der Düse",
        "清理喷嘴头",
        "Czyszczenie końcówki dyszy",
    ),
    "Checking Extruder Temperature": (
        "Verificando a temperatura da extrusora",
        "Comprobando la temperatura del extrusor",
        "Überprüfen der Extrudertemperatur",
        "检查挤出温度",
        "Sprawdzanie temperatury ekstrudera",
    ),
    "Paused by User": (
        "Pausado pelo usuário",
        "Pausado por el usuario",
        "Vom Benutzer pausiert",
        "已被用户暂停",
        "Wstrzymano przez użytkownika",
    ),
    "Paused: Front Cover Removed": (
        "Pausa (tampa frontal removida)",
        "Pausa (se cayó la tapa delantera)",
        "Pause (Frontabdeckung abgefallen)",
        "暂停（前盖脱落）",
        "Pauza: zdjęta przednia pokrywa",
    ),
    "Calibrating Extrusion Flow": (
        "Calibrando o fluxo de extrusão",
        "Calibrando el flujo de extrusión",
        "Extrusionsfluss wird kalibriert",
        "校准挤出流量",
        "Kalibracja przepływu",
    ),
    "Paused: Nozzle Temperature Fault": (
        "Pausa (falha na temperatura do bico)",
        "Pausa (fallo en la temperatura de la boquilla)",
        "Pause (Düsentemperaturstörung)",
        "暂停（喷嘴温度故障）",
        "Pauza: błąd temperatury dyszy",
    ),
    "Paused: Bed Temperature Fault": (
        "Pausa (falha na temperatura da mesa)",
        "Pausa (fallo en la temperatura de la cama caliente)",
        "Pause (Heizbetttemperaturstörung)",
        "暂停（热床温度故障）",
        "Pauza: błąd temperatury stołu",
    ),
    "Unloading Filament": (
        "Descarregando o filamento",
        "Descarga de filamento",
        "Entladen des Filaments",
        "耗材丝退料中",
        "Wyładowywanie filamentu",
    ),
    "Paused: Skipped Step": (
        "Pausa (perda de passos)",
        "Pausa (pasos perdidos)",
        "Pause (Schrittverlust)",
        "暂停（电机丢步）",
        "Pauza: zgubione kroki",
    ),
    "Loading Filament": (
        "Carregando o filamento",
        "Carga de filamento",
        "Laden des Filaments",
        "耗材丝进料中",
        "Ładowanie filamentu",
    ),
    "Calibrating Motor Noise": (
        "Calibrando o ruído do motor",
        "Calibrando el ruido del motor",
        "Motorgeräusch wird kalibriert",
        "电机噪音校准",
        "Kalibracja szumu silników",
    ),
    "Paused: AMS Lost": (
        "Pausa (AMS desconectado)",
        "Pausa (AMS perdido)",
        "Pause (AMS getrennt)",
        "暂停（AMS 断开）",
        "Pauza: utracono AMS",
    ),
    "Paused: Heat Break Fan": (
        "Pausa (ventoinha do heatbreak)",
        "Pausa (baja velocidad del ventilador del disipador térmico)",
        "Pause (zu kleine Geschwindigkeit des Heatbreak-Lüfters)",
        "暂停（散热风扇低速）",
        "Pauza: wentylator heatbreaka",
    ),
    "Paused: Chamber Temperature Fault": (
        "Pausa (falha na temperatura da câmara)",
        "Pausa (problema con el control de temperatura de la recámara)",
        "Pause (Kammertemperaturregelungsproblem)",
        "暂停（腔体温度控制问题）",
        "Pauza: błąd temperatury komory",
    ),
    "Cooling Chamber": (
        "Resfriando a câmara",
        "Enfriando la recámara",
        "Kühlung der Kammer",
        "腔体降温中",
        "Chłodzenie komory",
    ),
    "Paused by G-code": (
        "Pausado por G-code",
        "Pausa (G-code insertado por el usuario)",
        "Pause (vom Benutzer eingefügter G-Code)",
        "暂停（用户插入的 G-code）",
        "Wstrzymano przez G-code",
    ),
    "Motor Noise Showoff": (
        "Demonstração do ruído do motor",
        "Demostración del ruido del motor",
        "Motorgeräusch-Showoff",
        "电机噪音校准结果展示",
        "Pokaz szumu silników",
    ),
    "Paused: Nozzle Covered": (
        "Pausa (bico coberto de filamento)",
        "Pausa (boquilla cubierta de filamento)",
        "Pause (Düse mit Filament bedeckt)",
        "暂停（喷嘴被耗材丝包裹）",
        "Pauza: zasłonięta dysza",
    ),
    "Paused: Cutter Error": (
        "Pausa (erro do cortador)",
        "Pausa (error del cortador)",
        "Pause (Schneidfehler)",
        "暂停（切刀错误）",
        "Pauza: błąd obcinaka",
    ),
    "Paused: First Layer Error": (
        "Pausa (erro na primeira camada)",
        "Pausa (error en la primera capa)",
        "Pause (Fehler in der ersten Schicht)",
        "暂停（首层错误）",
        "Pauza: błąd pierwszej warstwy",
    ),
    "Paused: Nozzle Clog": (
        "Pausa (bico entupido)",
        "Pausa (boquilla obstruida)",
        "Pause (Düsenverstopfung)",
        "暂停（喷嘴堵塞）",
        "Pauza: zatkana dysza",
    ),
}
_TEXTS = {lang: {en: row[i] for en, row in _TEXT_ROWS.items()} for i, lang in enumerate(_TEXT_LANGS)}


def settings_boot(current_url: str, low_stock_grams: float, plate_check: bool = True,
                  plate_margin: int = _core.DEFAULT_MARGIN, weight: str = "both", cart: bool = False,
                  source: str = "spoolman", progress: dict | None = None, columns: int = 1,
                  stats: dict | None = None, wizard: bool = False, verified_url: str = "") -> dict:
    return {
        "url": current_url or "", "verified_url": verified_url, "default_url": _core.DEFAULT_SPOOLMAN_URL,
        "source": _sources.parse_source(source), "low_stock": low_stock_grams, "plate_check": bool(plate_check),
        "plate_margin": plate_margin, "weight_display": _core.parse_weights(weight), "show_cart": bool(cart),
        "spool_columns": _core.parse_columns(columns), "spool_view": _core.spool_view(), "progress": _core.parse_progress(progress), "stats": _core.parse_stats(stats),
        "display": _core.display_settings(), "drying": _core.drying_settings(), "presets": _filament_profiles.presets_settings(),
        "parents": _filament_profiles.parent_bases(_filament_profiles._ui_snap.get("parents") or []), "cur_code": _stats._cur["code"] or "EUR",
        "wizard": bool(wizard), "log_path": str(_core.LOG_FILE), "auto_keep_slots": _capabilities.auto_keep_on(), "refresh_s": _capabilities.refresh_secs(),
        "rfid_skipped": _rfid.rfid_skipped_count(),
        "save_calibration": _spoolman_sync.calibration_mode(),
    }


def page_html(mode: str, view: str = "main", settings: dict | None = None, page: str = "") -> str:
    """The page for one surface, or error_page() when building it fails: OrcaSlicer leaves the tab an empty grey
    panel when get_ui() raises."""
    try:
        return _page_html(mode, view, settings, page)
    except Exception as exc:  # noqa: BLE001 - shown on the page and logged instead
        _core.log.exception("Could not build the %s page", mode)
        return error_page(exc)


def error_page(error: object) -> str:
    """A small page that says the real one failed, with the error and a Copy diagnostics button, instead of a
    blank tab. No settings, no app.html: only what is certain to work. Never raises."""
    try:
        return _error_page(error)
    except Exception:  # noqa: BLE001 - last resort: still not a blank tab
        _core.log.exception("Could not build the error page")
        return "<!doctype html><meta charset=utf-8><p>Spooler could not open its page. See spooler.log.</p>"


def _error_page(error: object) -> str:
    detail = f"{type(error).__name__}: {error}" if isinstance(error, BaseException) else str(error)
    diagnostics = "\n".join((
        f"{_core.PLUGIN_NAME} {_core.PLUGIN_VERSION} ({_core.BUILD_TARGET} build)",
        f"Python {sys.version.split()[0]}, {sys.platform}",
        f"Error: {_core.redact(detail)}",
        f"Log: {_core.LOG_FILE}",
    ))
    try:
        title, copy = tr("Spooler could not open its page."), tr("Copy diagnostics")
        log_at = tr("The log is at {path}.", path=_core.LOG_FILE)
    except Exception:  # noqa: BLE001 - the error page must not fail in turn
        title, copy, log_at = "Spooler could not open its page.", "Copy diagnostics", f"The log is at {_core.LOG_FILE}."
    esc = html.escape
    return f"""<!doctype html><html><head><meta charset="utf-8"><style>
body{{font:14px system-ui,sans-serif;margin:24px;color:#e6e6e6;background:#2b2b2b}}
@media (prefers-color-scheme:light){{body{{color:#222;background:#f4f4f4}}}}
h1{{font-size:16px}}pre{{white-space:pre-wrap;user-select:text;padding:8px;border:1px solid #8884}}
</style></head><body><h1>{esc(title)}</h1>
<p>{esc(log_at)}</p>
<pre id="d">{esc(diagnostics)}</pre><button id="c">{esc(copy)}</button>
<script>document.getElementById("c").onclick=function(){{var r=document.createRange();
r.selectNodeContents(document.getElementById("d"));var s=getSelection();s.removeAllRanges();s.addRange(r);
try{{document.execCommand("copy")}}catch(e){{}}}};</script></body></html>"""


def _page_html(mode: str, view: str = "main", settings: dict | None = None, page: str = "") -> str:
    """The page for one surface: "tab" (spool views + Settings), "main" (spool window) or "settings" (window).

    ``page`` is the settings page to open first (s-src, ...), as a "Settings" link in the spool window asked."""
    _tab.text_language(fresh=True)  # built on the UI thread: Python's own texts follow the same choice
    boot = {
        "mode": mode, "view": view, "version": _core.PLUGIN_VERSION, "lang": _tab.host_language(), "pref": _tab.ui_language(),
        "low_stock_default": _core.LOW_DEFAULT, "refresh_ms": _core.REFRESH_SECS * 1000, "display_defaults": _core.DISPLAY_DEFAULTS,
        "own_fields": sorted(_editor.EDITOR_OWN), "logo": _tab.LOGO_DATA_URI,
        "page": page if isinstance(page, str) and re.fullmatch(r"s-[a-z]{1,16}", page) else "",
        "settings": settings or settings_boot(_core.get_settings().get("spoolman_url", ""), _core.parse_low(_core.get_settings().get("low_stock_grams"))),
    }
    return fit_webview(_tab.ui_page().replace("__BOOT__", _tab._json_for_html(boot), 1))


# OrcaSlicer on Windows shows a page through WebView2, which takes at most 2 MiB once the page is base64-encoded:
# 1.5 MiB of UTF-8. A bigger page stays blank (0.30.0's tab was 1,573,958 bytes, 1,094 over, and never loaded).
WEBVIEW_PAGE_LIMIT = 1_572_864
_FONT_DATA = re.compile(r"url\(data:font/[\w.+-]+;base64,[A-Za-z0-9+/=]+\)(?:\s*format\([^)]*\))?")   # local() takes no format()


def fit_webview(html: str) -> str:
    """The page, without its embedded web fonts when they would push it over WEBVIEW_PAGE_LIMIT: it then draws
    in the system font instead of staying blank."""
    if len(html.encode("utf-8")) <= WEBVIEW_PAGE_LIMIT:
        return html
    lighter = _FONT_DATA.sub('local("Manrope")', html)
    size = len(lighter.encode("utf-8"))
    if size > WEBVIEW_PAGE_LIMIT:
        _core.log.warning("The page is %d bytes, over OrcaSlicer's %d on Windows; it may stay blank", size, WEBVIEW_PAGE_LIMIT)
    return lighter


def main_html() -> str:
    return page_html("main")


def settings_html(current_url: str, spoolman_info: dict, low_stock_grams: float,
                  plate_check: bool = True, plate_margin: int = _core.DEFAULT_MARGIN,
                  weight: str = "both", cart: bool = False, source: str = "spoolman",
                  progress: dict | None = None, columns: int = 1, stats: dict | None = None,
                  wizard: bool = False, page: str = "") -> str:
    """``spoolman_info`` describes the saved URL, not whatever is typed in the field."""
    verified_url = _sources.clean_url(current_url) if spoolman_info.get("ok") else ""
    return page_html("settings", "settings", settings_boot(
        current_url, low_stock_grams, plate_check, plate_margin, weight, cart, source, progress, columns, stats,
        wizard, verified_url), page)


def tab_html(initial_view: str, current_url: str, low_stock_grams: float,
             plate_check: bool = True, plate_margin: int = _core.DEFAULT_MARGIN,
             weight: str = "both", cart: bool = False, source: str = "spoolman",
             progress: dict | None = None, columns: int = 1, stats: dict | None = None,
             wizard: bool = False) -> str:
    """The spool views and Settings as two views of one page (the native tab)."""
    return page_html("tab", "main" if initial_view == "main" else "settings", settings_boot(
        current_url, low_stock_grams, plate_check, plate_margin, weight, cart, source, progress, columns, stats, wizard))


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import capabilities as _capabilities  # noqa: E402
from . import editor as _editor  # noqa: E402
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
from . import stats as _stats  # noqa: E402
from . import tab as _tab  # noqa: E402
